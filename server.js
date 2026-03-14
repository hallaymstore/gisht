const http = require("http");
const net = require("net");
const fs = require("fs/promises");
const path = require("path");
const crypto = require("crypto");
const { spawn } = require("child_process");
const { URL } = require("url");
const { promisify } = require("util");
const sharp = require("sharp");
const ffmpegStatic = require("ffmpeg-static");

const PUBLIC_DIR = path.join(process.cwd(), "public");
const PORT = Number(process.env.PORT || 4000);
const MONGODB_URI = String(process.env.MONGODB_URI || "mongodb+srv://abumafia0:abumafia0@abumafia.h1trttg.mongodb.net/gisht?appName=abumafia").trim();
const DB_NAME = process.env.DB_NAME || "gisht";
const APP_TIMEZONE = process.env.APP_TIMEZONE || "Asia/Tashkent";
const SESSION_COOKIE = "gisht_session";
const SESSION_TTL_DAYS = Number(process.env.SESSION_TTL_DAYS || 30);
const MAX_BODY_SIZE = 10 * 1024 * 1024;
const MONGO_CONNECT_TIMEOUT_MS = Number(process.env.MONGO_CONNECT_TIMEOUT_MS || 2000);
const LOCAL_DB_FILE = path.join(process.cwd(), ".gisht-local-db.json");
const WORK_TYPES = [
  { key: "parmofka", label: "Parmofka" },
  { key: "klidka", label: "Klidka" },
  { key: "bont", label: "Bont" },
  { key: "sotka", label: "Sotka" },
  { key: "pogruska", label: "Pogruska" },
  { key: "kochigar", label: "Kochigar" },
];
const WORK_TYPE_KEYS = WORK_TYPES.map((item) => item.key);
const WORK_TYPE_LABELS = Object.fromEntries(WORK_TYPES.map((item) => [item.key, item.label]));
const WORKER_TRANSACTION_TYPES = {
  advance: { label: "Avans", effect: "debit" },
  loan: { label: "Qarz", effect: "debit" },
  deduction: { label: "Ushlab qolish", effect: "debit" },
  bonus: { label: "Bonus", effect: "credit" },
  correction_in: { label: "Qo'shimcha kirim", effect: "credit" },
  correction_out: { label: "Qo'shimcha chiqim", effect: "debit" },
};
const CAMERA_MODEL_PRESETS = {
  custom: {
    key: "custom",
    label: "Boshqa IP kamera",
    description: "Snapshot API yoki RTSP manzilini qo'lda kiritish uchun.",
    snapshotExample: "http://camera-ip/snapshot.jpg",
    streamExample: "rtsp://camera-ip:554/stream",
    httpExample: "http://camera-ip/mjpeg",
  },
  axis_vapix_generic: {
    key: "axis_vapix_generic",
    label: "Axis VAPIX IP kamera",
    description: "Axis kameralarida odatda VAPIX snapshot, MJPEG va RTSP yoqilgan bo'ladi.",
    snapshotExample: "http://camera-ip/axis-cgi/jpg/image.cgi",
    streamExample: "rtsp://camera-ip/axis-media/media.amp",
    httpExample: "http://camera-ip/axis-cgi/mjpg/video.cgi",
  },
  hikvision_ds_2cd2643g2_izs: {
    key: "hikvision_ds_2cd2643g2_izs",
    label: "Hikvision DS-2CD2643G2-IZS",
    description: "4 MP bullet IP kamera, ONVIF/ISAPI/RTSP profiliga mos.",
    snapshotExample: "http://camera-ip/ISAPI/Streaming/channels/101/picture",
    streamExample: "rtsp://camera-ip:554/Streaming/Channels/101",
    httpExample: "http://camera-ip/ISAPI/Streaming/channels/101/httpPreview",
  },
};
const CAMERA_MODEL_KEYS = Object.keys(CAMERA_MODEL_PRESETS);

const scryptAsync = promisify(crypto.scrypt);
const protectedPages = {
  "/admin.html": ["admin"],
  "/organizer.html": ["organizer"],
  "/worker.html": ["worker"],
  "/profile.html": ["admin", "organizer", "worker"],
};

let mongoClient;
let MongoClient;
let ObjectId;
let collections;
let storageMode = "mongo";
const cameraMonitorService = {
  runtimes: new Map(),
  ready: false,
  reloading: null,
};
const demoCameraState = {
  requestCount: 0,
};

async function loadMongoDriver() {
  try {
    const mongodb = await import("mongodb");
    MongoClient = mongodb.MongoClient;
    ObjectId = mongodb.ObjectId;
  } catch (error) {
    MongoClient = null;
    ObjectId = null;
    console.warn("`mongodb` paketi topilmadi. Server local storage rejimida ishlaydi.");
  }
}

function cloneValue(value) {
  if (typeof structuredClone === "function") {
    return structuredClone(value);
  }
  return JSON.parse(JSON.stringify(value));
}

function randomHex(length = 24) {
  return crypto.randomBytes(Math.ceil(length / 2)).toString("hex").slice(0, length);
}

class LocalObjectId {
  constructor(value) {
    this.value = String(value || randomHex(24));
  }

  toString() {
    return this.value;
  }

  toJSON() {
    return this.value;
  }

  valueOf() {
    return this.value;
  }

  static isValid(value) {
    return /^[a-f0-9]{24}$/i.test(String(value || ""));
  }
}

function normalizeIdString(value) {
  if (typeof value === "string") {
    return value;
  }
  if (typeof value === "number" || typeof value === "bigint") {
    return String(value);
  }
  if (!value || typeof value !== "object") {
    return "";
  }
  if (typeof value.value === "string") {
    return value.value;
  }
  if (typeof value.$oid === "string") {
    return value.$oid;
  }
  if (typeof value.toHexString === "function") {
    const hex = value.toHexString();
    if (hex && hex !== "[object Object]") {
      return hex;
    }
  }
  if (value.buffer && ArrayBuffer.isView(value.buffer)) {
    return Buffer.from(value.buffer).toString("hex");
  }
  if (typeof value.toString === "function" && value.toString !== Object.prototype.toString) {
    const raw = value.toString();
    if (raw && raw !== "[object Object]") {
      return raw;
    }
  }
  return "";
}

function toStoredId(value) {
  const normalized = normalizeIdString(value);
  if (!normalized || !ObjectId?.isValid(normalized)) {
    return null;
  }
  return storageMode === "mongo" ? new ObjectId(normalized) : normalized;
}

function normalizeComparable(value) {
  if (value instanceof Date) {
    return value.getTime();
  }
  const idValue = normalizeIdString(value);
  if (idValue) {
    return idValue;
  }
  if (value && typeof value === "object" && typeof value.toString === "function") {
    return value.toString();
  }
  return value;
}

function isPlainObject(value) {
  return value && typeof value === "object" && !Array.isArray(value) && !(value instanceof Date);
}

function matchesQuery(document, query = {}) {
  return Object.entries(query).every(([key, expected]) => {
    const actual = document[key];

    if (Array.isArray(actual)) {
      if (isPlainObject(expected) && Array.isArray(expected.$in)) {
        return actual.some((value) =>
          expected.$in.some((candidate) => normalizeComparable(candidate) === normalizeComparable(value)));
      }
      return actual.some((value) => normalizeComparable(value) === normalizeComparable(expected));
    }

    if (isPlainObject(expected) && Array.isArray(expected.$in)) {
      return expected.$in.some((candidate) => normalizeComparable(candidate) === normalizeComparable(actual));
    }

    return normalizeComparable(expected) === normalizeComparable(actual);
  });
}

function normalizeSortValue(value) {
  if (value instanceof Date) {
    return value.getTime();
  }

  if (typeof value === "string") {
    const parsed = Date.parse(value);
    if (!Number.isNaN(parsed) && value.includes("-")) {
      return parsed;
    }
    return value.toLowerCase();
  }

  if (value && typeof value === "object" && typeof value.toString === "function") {
    return value.toString();
  }

  return value ?? 0;
}

class LocalCursor {
  constructor(items) {
    this.items = items;
  }

  sort(spec = {}) {
    const entries = Object.entries(spec);
    this.items.sort((left, right) => {
      for (const [field, direction] of entries) {
        const a = normalizeSortValue(left[field]);
        const b = normalizeSortValue(right[field]);
        if (a === b) {
          continue;
        }
        if (a > b) {
          return direction >= 0 ? 1 : -1;
        }
        return direction >= 0 ? -1 : 1;
      }
      return 0;
    });
    return this;
  }

  limit(count) {
    this.items = this.items.slice(0, count);
    return this;
  }

  async toArray() {
    return this.items.map((item) => cloneValue(item));
  }
}

class LocalCollection {
  constructor(name, state, persist) {
    this.name = name;
    this.state = state;
    this.persist = persist;
  }

  get records() {
    return this.state[this.name];
  }

  async createIndex() {
    return `${this.name}_local_index`;
  }

  async findOne(query = {}) {
    const found = this.records.find((item) => matchesQuery(item, query));
    return found ? cloneValue(found) : null;
  }

  find(query = {}) {
    const items = this.records.filter((item) => matchesQuery(item, query)).map((item) => cloneValue(item));
    return new LocalCursor(items);
  }

  async countDocuments(query = {}) {
    return this.records.filter((item) => matchesQuery(item, query)).length;
  }

  async insertOne(document) {
    const payload = cloneValue(document);
    if (!payload._id) {
      payload._id = randomHex(24);
    } else {
      payload._id = normalizeComparable(payload._id);
    }
    this.records.push(payload);
    await this.persist();
    return { insertedId: payload._id };
  }

  async insertMany(documents = []) {
    const insertedIds = {};
    documents.forEach((document, index) => {
      const payload = cloneValue(document);
      payload._id = payload._id ? normalizeComparable(payload._id) : randomHex(24);
      this.records.push(payload);
      insertedIds[index] = payload._id;
    });
    await this.persist();
    return { insertedCount: documents.length, insertedIds };
  }

  async updateOne(query = {}, update = {}) {
    const target = this.records.find((item) => matchesQuery(item, query));
    if (!target) {
      return { matchedCount: 0, modifiedCount: 0 };
    }

    if (update.$set && isPlainObject(update.$set)) {
      Object.assign(target, cloneValue(update.$set));
    }

    await this.persist();
    return { matchedCount: 1, modifiedCount: 1 };
  }

  async deleteOne(query = {}) {
    const index = this.records.findIndex((item) => matchesQuery(item, query));
    if (index === -1) {
      return { deletedCount: 0 };
    }
    this.records.splice(index, 1);
    await this.persist();
    return { deletedCount: 1 };
  }

  async deleteMany(query = {}) {
    const before = this.records.length;
    this.state[this.name] = this.records.filter((item) => !matchesQuery(item, query));
    const deletedCount = before - this.state[this.name].length;
    if (deletedCount > 0) {
      await this.persist();
    }
    return { deletedCount };
  }
}

async function createLocalCollections() {
  let state = {
    users: [],
    sessions: [],
    tasks: [],
    contents: [],
    settings: [],
    notifications: [],
    payrolls: [],
    workLogs: [],
    workerTransactions: [],
    customerPayments: [],
    cameraCounts: [],
  };

  try {
    const raw = await fs.readFile(LOCAL_DB_FILE, "utf8");
    const parsed = parseJson(raw);
    if (parsed && typeof parsed === "object") {
      state = {
        users: Array.isArray(parsed.users) ? parsed.users : [],
        sessions: Array.isArray(parsed.sessions) ? parsed.sessions : [],
        tasks: Array.isArray(parsed.tasks) ? parsed.tasks : [],
        contents: Array.isArray(parsed.contents) ? parsed.contents : [],
        settings: Array.isArray(parsed.settings) ? parsed.settings : [],
        notifications: Array.isArray(parsed.notifications) ? parsed.notifications : [],
        payrolls: Array.isArray(parsed.payrolls) ? parsed.payrolls : [],
        workLogs: Array.isArray(parsed.workLogs) ? parsed.workLogs : [],
        workerTransactions: Array.isArray(parsed.workerTransactions) ? parsed.workerTransactions : [],
        customerPayments: Array.isArray(parsed.customerPayments) ? parsed.customerPayments : [],
        cameraCounts: Array.isArray(parsed.cameraCounts) ? parsed.cameraCounts : [],
      };
    }
  } catch (error) {
    if (error.code !== "ENOENT") {
      console.warn(`Local storage faylini o'qib bo'lmadi: ${error.message}`);
    }
  }

  let persistQueue = Promise.resolve();
  const persist = async () => {
    persistQueue = persistQueue.then(() =>
      fs.writeFile(LOCAL_DB_FILE, JSON.stringify(state, null, 2), "utf8"),
    );
    return persistQueue;
  };

  return {
    users: new LocalCollection("users", state, persist),
    sessions: new LocalCollection("sessions", state, persist),
    tasks: new LocalCollection("tasks", state, persist),
    contents: new LocalCollection("contents", state, persist),
    settings: new LocalCollection("settings", state, persist),
    notifications: new LocalCollection("notifications", state, persist),
    payrolls: new LocalCollection("payrolls", state, persist),
    workLogs: new LocalCollection("workLogs", state, persist),
    workerTransactions: new LocalCollection("workerTransactions", state, persist),
    customerPayments: new LocalCollection("customerPayments", state, persist),
    cameraCounts: new LocalCollection("cameraCounts", state, persist),
  };
}

function getYmd(date = new Date()) {
  const parts = new Intl.DateTimeFormat("en-US", {
    timeZone: APP_TIMEZONE,
    year: "numeric",
    month: "2-digit",
    day: "2-digit",
  }).formatToParts(date);

  const byType = Object.fromEntries(parts.map((item) => [item.type, item.value]));
  return `${byType.year}-${byType.month}-${byType.day}`;
}

function getTomorrowYmd() {
  return getYmd(new Date(Date.now() + 24 * 60 * 60 * 1000));
}

function slugify(value = "") {
  return String(value)
    .normalize("NFKD")
    .replace(/[^\w\s-]/g, "")
    .trim()
    .toLowerCase()
    .replace(/[\s_-]+/g, "-")
    .replace(/^-+|-+$/g, "");
}

function normalizeUsername(value = "") {
  return String(value).trim().toLowerCase();
}

function safeString(value, max = 2000) {
  return String(value || "").trim().slice(0, max);
}

function normalizeWorkType(value, fallback = "") {
  const workType = safeString(value, 20).toLowerCase();
  return WORK_TYPE_KEYS.includes(workType) ? workType : fallback;
}

function workTypeLabel(value) {
  return WORK_TYPE_LABELS[normalizeWorkType(value)] || "";
}

function getDefaultWorkRates() {
  return Object.fromEntries(WORK_TYPES.map((item) => [item.key, 0]));
}

function defaultCameraSettings() {
  const preset = CAMERA_MODEL_PRESETS.hikvision_ds_2cd2643g2_izs;
  return {
    enabled: false,
    modelKey: preset.key,
    modelLabel: preset.label,
    modelDescription: preset.description,
    streamMode: "snapshot",
    snapshotUrl: "",
    streamUrl: "",
    authType: "basic",
    username: "",
    password: "",
    apiToken: "",
    tokenQueryKey: "token",
    ffmpegPath: ffmpegStatic || "ffmpeg",
    rtspTransport: "tcp",
    workType: "parmofka",
    lineStartX: 0.5,
    lineStartY: 0.08,
    lineEndX: 0.5,
    lineEndY: 0.92,
    frameIntervalMs: 900,
    motionThreshold: 28,
    minBlobArea: 140,
    maxBlobArea: 12000,
    trackerDistancePx: 60,
    snapshotExample: preset.snapshotExample,
    streamExample: preset.streamExample,
    httpExample: preset.httpExample,
  };
}

function normalizeWorkRates(input = {}) {
  return Object.fromEntries(
    WORK_TYPES.map(({ key }) => [key, Math.max(0, roundMoney(input[key] || 0))]),
  );
}

function normalizeCameraModelKey(value, fallback = "custom") {
  const key = safeString(value, 60).toLowerCase();
  return CAMERA_MODEL_KEYS.includes(key) ? key : fallback;
}

function normalizeCameraStreamMode(value, fallback = "snapshot") {
  const mode = safeString(value, 30).toLowerCase();
  return ["snapshot", "rtsp", "http"].includes(mode) ? mode : fallback;
}

function normalizeCameraAuthType(value, fallback = "basic") {
  const authType = safeString(value, 30).toLowerCase();
  return ["none", "basic", "bearer", "query"].includes(authType) ? authType : fallback;
}

function clampUnit(value, fallback = 0.5) {
  const number = parseNumber(value, fallback);
  if (!Number.isFinite(number)) {
    return fallback;
  }
  return Math.max(0, Math.min(1, number));
}

function normalizeCameraSettings(input = {}) {
  const defaults = defaultCameraSettings();
  const modelKey = normalizeCameraModelKey(input.modelKey, defaults.modelKey);
  const preset = CAMERA_MODEL_PRESETS[modelKey] || CAMERA_MODEL_PRESETS.custom;
  return {
    enabled: parseBoolean(input.enabled, defaults.enabled),
    modelKey,
    modelLabel: preset.label,
    modelDescription: preset.description,
    streamMode: normalizeCameraStreamMode(input.streamMode, defaults.streamMode),
    snapshotUrl: safeString(input.snapshotUrl, 4000),
    streamUrl: safeString(input.streamUrl, 4000),
    authType: normalizeCameraAuthType(input.authType, defaults.authType),
    username: safeString(input.username, 120),
    password: safeString(input.password, 200),
    apiToken: safeString(input.apiToken, 4000),
    tokenQueryKey: safeString(input.tokenQueryKey, 60) || defaults.tokenQueryKey,
    ffmpegPath: safeString(input.ffmpegPath, 200) || defaults.ffmpegPath,
    rtspTransport: safeString(input.rtspTransport, 10).toLowerCase() === "udp" ? "udp" : defaults.rtspTransport,
    workType: normalizeWorkType(input.workType, defaults.workType),
    lineStartX: clampUnit(input.lineStartX, defaults.lineStartX),
    lineStartY: clampUnit(input.lineStartY, defaults.lineStartY),
    lineEndX: clampUnit(input.lineEndX, defaults.lineEndX),
    lineEndY: clampUnit(input.lineEndY, defaults.lineEndY),
    frameIntervalMs: clampNumber(input.frameIntervalMs || defaults.frameIntervalMs, 250, 5000, defaults.frameIntervalMs),
    motionThreshold: clampNumber(input.motionThreshold || defaults.motionThreshold, 5, 255, defaults.motionThreshold),
    minBlobArea: clampNumber(input.minBlobArea || defaults.minBlobArea, 10, 200000, defaults.minBlobArea),
    maxBlobArea: clampNumber(input.maxBlobArea || defaults.maxBlobArea, 10, 1_000_000, defaults.maxBlobArea),
    trackerDistancePx: clampNumber(input.trackerDistancePx || defaults.trackerDistancePx, 5, 500, defaults.trackerDistancePx),
    snapshotExample: preset.snapshotExample,
    streamExample: preset.streamExample,
    httpExample: preset.httpExample,
  };
}

function normalizeCameraWorkerIds(value) {
  const list = Array.isArray(value)
    ? value
    : typeof value === "string"
      ? value.split(",")
      : [];
  return [...new Set(list.map((item) => safeString(item, 40)).filter(Boolean))].slice(0, 10);
}

function normalizeCameraCountDirection(value, fallback = "both") {
  const direction = safeString(value, 40).toLowerCase();
  return ["both", "negative_to_positive", "positive_to_negative"].includes(direction) ? direction : fallback;
}

function defaultCameraMonitor(index = 1) {
  return {
    id: randomHex(16),
    name: `Kamera ${index}`,
    areaName: `Zona ${index}`,
    notes: "",
    enabled: false,
    autoSyncWorkLog: true,
    workerIds: [],
    countDirection: "negative_to_positive",
    createdAt: new Date(),
    updatedAt: new Date(),
    ...defaultCameraSettings(),
  };
}

function normalizeCameraMonitor(input = {}, fallbackMonitor = {}) {
  const defaults = defaultCameraMonitor();
  const base = normalizeCameraSettings({
    ...defaults,
    ...fallbackMonitor,
    ...input,
  });
  return {
    id: safeString(input.id || fallbackMonitor.id || defaults.id, 40) || defaults.id,
    name: safeString(input.name || fallbackMonitor.name || defaults.name, 80) || defaults.name,
    areaName: safeString(input.areaName || fallbackMonitor.areaName || defaults.areaName, 120) || defaults.areaName,
    notes: safeString(input.notes || fallbackMonitor.notes || "", 400),
    autoSyncWorkLog: parseBoolean(
      typeof input.autoSyncWorkLog !== "undefined" ? input.autoSyncWorkLog : fallbackMonitor.autoSyncWorkLog,
      true,
    ),
    workerIds: normalizeCameraWorkerIds(
      typeof input.workerIds !== "undefined" ? input.workerIds : fallbackMonitor.workerIds,
    ),
    countDirection: normalizeCameraCountDirection(
      typeof input.countDirection !== "undefined" ? input.countDirection : fallbackMonitor.countDirection,
      "negative_to_positive",
    ),
    createdAt: fallbackMonitor.createdAt || new Date(),
    updatedAt: new Date(),
    ...base,
  };
}

function normalizeCameraSystemSettings(input = {}) {
  const monitorsInput = Array.isArray(input.monitors) ? input.monitors : [];
  const seenIds = new Set();
  const monitors = monitorsInput
    .map((item, index) => normalizeCameraMonitor(item, defaultCameraMonitor(index + 1)))
    .filter((item) => {
      if (!item.id || seenIds.has(item.id)) {
        return false;
      }
      seenIds.add(item.id);
      return true;
    });

  return {
    monitors,
  };
}

function normalizeWorkerTransactionType(value, fallback = "advance") {
  const type = safeString(value, 30).toLowerCase();
  return WORKER_TRANSACTION_TYPES[type] ? type : fallback;
}

function workerTransactionMeta(type) {
  return WORKER_TRANSACTION_TYPES[normalizeWorkerTransactionType(type)] || WORKER_TRANSACTION_TYPES.advance;
}

function parseBoolean(value, fallback = false) {
  if (typeof value === "boolean") {
    return value;
  }
  if (typeof value === "string") {
    return value === "true" || value === "1";
  }
  return fallback;
}

function parseJson(text, fallback = null) {
  try {
    return JSON.parse(text);
  } catch {
    return fallback;
  }
}

function parseTags(input) {
  if (Array.isArray(input)) {
    return input.map((item) => safeString(item, 40)).filter(Boolean).slice(0, 8);
  }
  if (typeof input === "string") {
    return input
      .split(",")
      .map((item) => safeString(item, 40))
      .filter(Boolean)
      .slice(0, 8);
  }
  return [];
}

function parseNumber(value, fallback = 0) {
  const number = Number(value);
  return Number.isFinite(number) ? number : fallback;
}

function clampNumber(value, min, max, fallback = min) {
  const number = parseNumber(value, fallback);
  return Math.min(max, Math.max(min, number));
}

function roundMoney(value) {
  return Math.round((parseNumber(value, 0) + Number.EPSILON) * 100) / 100;
}

function toMonthKey(value = new Date()) {
  const ymd = typeof value === "string" ? safeString(value, 10) : getYmd(value);
  return ymd.slice(0, 7);
}

function shiftYmd(ymd, days) {
  const [year, month, day] = String(ymd).split("-").map(Number);
  const utcDate = new Date(Date.UTC(year, month - 1, day));
  utcDate.setUTCDate(utcDate.getUTCDate() + Number(days || 0));
  return utcDate.toISOString().slice(0, 10);
}

function getMonthLastDay(monthKey) {
  const [year, month] = String(monthKey).split("-").map(Number);
  return new Date(Date.UTC(year, month, 0)).getUTCDate();
}

function buildMonthDate(monthKey, dayOfMonth) {
  const clampedDay = Math.min(getMonthLastDay(monthKey), clampNumber(dayOfMonth, 1, 31, 5));
  return `${monthKey}-${String(clampedDay).padStart(2, "0")}`;
}

function getWeekdayFromYmd(ymd) {
  const [year, month, day] = String(ymd).split("-").map(Number);
  const weekday = new Date(Date.UTC(year, month - 1, day)).getUTCDay();
  return weekday === 0 ? 7 : weekday;
}

function isYmdWithinRange(ymd, start, end) {
  return String(ymd) >= String(start) && String(ymd) <= String(end);
}

function sha256(value) {
  return crypto.createHash("sha256").update(value).digest("hex");
}

async function hashPassword(password) {
  const salt = crypto.randomBytes(16).toString("hex");
  const derived = await scryptAsync(password, salt, 64);
  return `${salt}:${derived.toString("hex")}`;
}

async function verifyPassword(password, storedHash) {
  if (!storedHash || !storedHash.includes(":")) {
    return false;
  }

  const [salt, hash] = storedHash.split(":");
  const derived = await scryptAsync(password, salt, 64);
  return crypto.timingSafeEqual(Buffer.from(hash, "hex"), derived);
}

function parseCookies(cookieHeader = "") {
  return cookieHeader.split(";").reduce((accumulator, part) => {
    const [key, ...rest] = part.trim().split("=");
    if (!key) {
      return accumulator;
    }
    accumulator[key] = decodeURIComponent(rest.join("="));
    return accumulator;
  }, {});
}

function sendJson(response, statusCode, payload, headers = {}) {
  response.writeHead(statusCode, {
    "Content-Type": "application/json; charset=utf-8",
    "Cache-Control": "no-store",
    ...headers,
  });
  response.end(JSON.stringify(payload));
}

function sendBuffer(response, statusCode, buffer, contentType = "application/octet-stream", headers = {}) {
  response.writeHead(statusCode, {
    "Content-Type": contentType,
    "Cache-Control": "no-store",
    "Content-Length": buffer.length,
    ...headers,
  });
  response.end(buffer);
}

function sendHtml(response, statusCode, html, headers = {}) {
  response.writeHead(statusCode, {
    "Content-Type": "text/html; charset=utf-8",
    ...headers,
  });
  response.end(html);
}

function redirect(response, location) {
  response.writeHead(302, { Location: location });
  response.end();
}

function buildSessionCookie(token, maxAgeSeconds = SESSION_TTL_DAYS * 24 * 60 * 60) {
  const parts = [
    `${SESSION_COOKIE}=${encodeURIComponent(token)}`,
    "Path=/",
    "HttpOnly",
    "SameSite=Lax",
    `Max-Age=${maxAgeSeconds}`,
  ];

  if (process.env.NODE_ENV === "production") {
    parts.push("Secure");
  }

  return parts.join("; ");
}

function buildClearCookie() {
  return [
    `${SESSION_COOKIE}=`,
    "Path=/",
    "HttpOnly",
    "SameSite=Lax",
    "Max-Age=0",
  ].join("; ");
}

async function readBody(request) {
  const chunks = [];
  let size = 0;

  for await (const chunk of request) {
    size += chunk.length;
    if (size > MAX_BODY_SIZE) {
      throw new Error("Body juda katta");
    }
    chunks.push(chunk);
  }

  const raw = Buffer.concat(chunks).toString("utf-8").trim();
  if (!raw) {
    return {};
  }
  const parsed = parseJson(raw);
  if (!parsed) {
    throw new Error("JSON noto'g'ri");
  }
  return parsed;
}

function mimeTypeFor(filePath) {
  const extension = path.extname(filePath).toLowerCase();
  if (extension === ".html") {
    return "text/html; charset=utf-8";
  }
  if (extension === ".json") {
    return "application/json; charset=utf-8";
  }
  if (extension === ".png") {
    return "image/png";
  }
  if (extension === ".jpg" || extension === ".jpeg") {
    return "image/jpeg";
  }
  if (extension === ".svg") {
    return "image/svg+xml";
  }
  return "application/octet-stream";
}

async function serveFile(response, filePath) {
  try {
    const content = await fs.readFile(filePath);
    response.writeHead(200, {
      "Content-Type": mimeTypeFor(filePath),
      "Cache-Control": "no-store",
    });
    response.end(content);
  } catch {
    sendHtml(response, 404, "<h1>404</h1><p>Sahifa topilmadi.</p>");
  }
}

function serializeUser(user) {
  const normalizedRole = normalizeRole(user.role, "worker");
  const assignedWorkType = normalizeWorkType(user.assignedWorkType, "");
  return {
    id: normalizeIdString(user._id),
    fullName: user.fullName,
    username: user.username,
    role: normalizedRole,
    positionTitle: normalizePositionTitle(normalizedRole, user.positionTitle),
    phone: user.phone || "",
    bio: user.bio || "",
    avatarUrl: user.avatarUrl || "",
    salaryAmount: roundMoney(user.salaryAmount || 0),
    salaryDayOfMonth: clampNumber(user.salaryDayOfMonth || 5, 1, 31, 5),
    assignedWorkType,
    assignedWorkTypeLabel: workTypeLabel(assignedWorkType),
    isActive: Boolean(user.isActive),
    createdAt: user.createdAt,
    lastLoginAt: user.lastLoginAt || null,
  };
}

function serializeContent(item) {
  return {
    id: normalizeIdString(item._id),
    type: item.type,
    title: item.title,
    slug: item.slug,
    excerpt: item.excerpt,
    body: item.body,
    imageUrl: item.imageUrl,
    priceLabel: item.priceLabel || "",
    tags: item.tags || [],
    isPublished: Boolean(item.isPublished),
    createdAt: item.createdAt,
    updatedAt: item.updatedAt || item.createdAt,
  };
}

function serializeTask(task, userMap = new Map()) {
  const createdBy = task.createdBy ? userMap.get(normalizeIdString(task.createdBy)) : null;
  const acceptedBy = task.acceptedBy ? userMap.get(normalizeIdString(task.acceptedBy)) : null;
  const completedBy = task.completedBy ? userMap.get(normalizeIdString(task.completedBy)) : null;
  const workType = normalizeWorkType(task.workType, "");

  return {
    id: normalizeIdString(task._id),
    type: task.type,
    workType,
    workTypeLabel: workTypeLabel(workType),
    customerName: task.customerName,
    quantity: task.quantity,
    scheduledDate: task.scheduledDate,
    status: task.status,
    notes: task.notes || "",
    unitPrice: roundMoney(task.unitPrice || 0),
    orderTotal: roundMoney(task.orderTotal || 0),
    paidAmount: roundMoney(task.paidAmount || 0),
    remainingAmount: roundMoney(task.remainingAmount || 0),
    paymentStatus: task.paymentStatus || (task.type === "delivery" ? "unpaid" : "not_applicable"),
    progressNotes: task.progressNotes || [],
    createdAt: task.createdAt,
    updatedAt: task.updatedAt || task.createdAt,
    acceptedAt: task.acceptedAt || null,
    completedAt: task.completedAt || null,
    createdBy,
    acceptedBy,
    completedBy,
  };
}

function serializeNotification(item, userMap = new Map()) {
  const recipient = item.userId ? userMap.get(normalizeIdString(item.userId)) : null;
  return {
    id: normalizeIdString(item._id),
    type: item.type || "info",
    title: item.title,
    body: item.body,
    link: item.link || "",
    isRead: Boolean(item.readAt),
    readAt: item.readAt || null,
    createdAt: item.createdAt,
    recipient,
    meta: item.meta || {},
  };
}

function serializePayroll(record, userMap = new Map()) {
  const user = record.userId ? userMap.get(normalizeIdString(record.userId)) : null;
  return {
    id: normalizeIdString(record._id),
    monthKey: record.monthKey,
    dueDate: record.dueDate,
    amount: roundMoney(record.amount || 0),
    status: record.status || "scheduled",
    paidAt: record.paidAt || null,
    notes: record.notes || "",
    user,
  };
}

function serializeWorkLog(record, userMap = new Map()) {
  const workers = Array.isArray(record.workerIds)
    ? record.workerIds.map((item) => userMap.get(normalizeIdString(item))).filter(Boolean)
    : [];
  const createdBy = record.createdBy ? userMap.get(normalizeIdString(record.createdBy)) : null;
  const workType = normalizeWorkType(record.workType, "");

  return {
    id: normalizeIdString(record._id),
    date: safeString(record.date, 10),
    workType,
    workTypeLabel: workTypeLabel(workType),
    quantity: Math.max(0, Math.round(parseNumber(record.quantity, 0))),
    ratePerBrick: roundMoney(record.ratePerBrick || 0),
    totalAmount: roundMoney(record.totalAmount || 0),
    shareAmount: roundMoney(record.shareAmount || 0),
    workers,
    notes: record.notes || "",
    source: record.source || "manual",
    cameraMonitorId: record.cameraMonitorId || "",
    cameraMonitorName: record.cameraMonitorName || "",
    createdAt: record.createdAt,
    updatedAt: record.updatedAt || record.createdAt,
    createdBy,
  };
}

function serializeWorkerTransaction(record, userMap = new Map()) {
  const worker = record.workerId ? userMap.get(normalizeIdString(record.workerId)) : null;
  const createdBy = record.createdBy ? userMap.get(normalizeIdString(record.createdBy)) : null;
  const type = normalizeWorkerTransactionType(record.type, "advance");
  const meta = workerTransactionMeta(type);

  return {
    id: normalizeIdString(record._id),
    date: safeString(record.date, 10),
    type,
    typeLabel: meta.label,
    effect: meta.effect,
    amount: roundMoney(record.amount || 0),
    note: record.note || "",
    worker,
    createdBy,
    createdAt: record.createdAt,
    updatedAt: record.updatedAt || record.createdAt,
  };
}

function mapDashboardPath(role) {
  if (role === "admin") {
    return "/admin.html";
  }
  if (role === "organizer") {
    return "/organizer.html";
  }
  return "/worker.html";
}

async function getSessionContext(request) {
  const cookies = parseCookies(request.headers.cookie || "");
  const token = cookies[SESSION_COOKIE];

  if (!token) {
    return null;
  }

  const tokenHash = sha256(token);
  const session = await collections.sessions.findOne({ tokenHash });

  if (!session || new Date(session.expiresAt) <= new Date()) {
    if (session) {
      await collections.sessions.deleteOne({ _id: session._id });
    }
    return { invalid: true };
  }

  const user = await collections.users.findOne({
    _id: session.userId,
    isActive: true,
  });

  if (!user) {
    await collections.sessions.deleteOne({ _id: session._id });
    return { invalid: true };
  }

  await collections.sessions.updateOne(
    { _id: session._id },
    { $set: { lastSeenAt: new Date() } },
  );

  return {
    session,
    user,
    safeUser: serializeUser(user),
  };
}

async function requireAuth(request, response, allowedRoles = null) {
  const context = await getSessionContext(request);

  if (!context || context.invalid) {
    sendJson(
      response,
      401,
      { error: "Tizimga kirish talab qilinadi." },
      context?.invalid ? { "Set-Cookie": buildClearCookie() } : {},
    );
    return null;
  }

  if (allowedRoles && !allowedRoles.includes(context.user.role)) {
    sendJson(response, 403, { error: "Bu bo'limga ruxsat yo'q." });
    return null;
  }

  return context;
}

async function createSession(user) {
  const token = crypto.randomBytes(48).toString("hex");
  const tokenHash = sha256(token);
  const expiresAt = new Date(Date.now() + SESSION_TTL_DAYS * 24 * 60 * 60 * 1000);

  await collections.sessions.insertOne({
    userId: user._id,
    tokenHash,
    role: user.role,
    createdAt: new Date(),
    lastSeenAt: new Date(),
    expiresAt,
  });

  return {
    token,
    expiresAt,
  };
}

function makePlaceholderDataUrl(title, start = "#f6ad80", end = "#7c2d12") {
  const safeTitle = String(title || "G'isht Zavodi").replace(/[<>&'"]/g, "");
  const svg = `
    <svg xmlns="http://www.w3.org/2000/svg" width="1200" height="800" viewBox="0 0 1200 800">
      <defs>
        <linearGradient id="bg" x1="0%" y1="0%" x2="100%" y2="100%">
          <stop offset="0%" stop-color="${start}" />
          <stop offset="100%" stop-color="${end}" />
        </linearGradient>
      </defs>
      <rect width="1200" height="800" rx="42" fill="url(#bg)" />
      <circle cx="190" cy="180" r="120" fill="rgba(255,255,255,0.16)" />
      <circle cx="1020" cy="120" r="80" fill="rgba(255,255,255,0.12)" />
      <rect x="86" y="560" width="1028" height="140" rx="28" fill="rgba(13,17,23,0.18)" />
      <text x="90" y="200" font-family="Verdana" font-size="44" fill="#fff" opacity="0.86">G'ISHT PLATFORM</text>
      <text x="90" y="310" font-family="Verdana" font-size="86" font-weight="700" fill="#fff">${safeTitle}</text>
      <text x="90" y="620" font-family="Verdana" font-size="36" fill="#fff" opacity="0.92">Sifatli ishlab chiqarish, nazorat va topshirish boshqaruvi</text>
    </svg>
  `.trim();

  return `data:image/svg+xml;charset=utf-8,${encodeURIComponent(svg)}`;
}

function hasCloudinaryConfig() {
  return Boolean(
    process.env.CLOUDINARY_CLOUD_NAME &&
      process.env.CLOUDINARY_API_KEY &&
      process.env.CLOUDINARY_API_SECRET,
  );
}

async function uploadToCloudinary(imageBase64, folder = "gisht-platform") {
  if (!hasCloudinaryConfig()) {
    return imageBase64;
  }

  const timestamp = Math.floor(Date.now() / 1000);
  const cloudName = process.env.CLOUDINARY_CLOUD_NAME;
  const apiKey = process.env.CLOUDINARY_API_KEY;
  const apiSecret = process.env.CLOUDINARY_API_SECRET;
  const signatureBase = `folder=${folder}&timestamp=${timestamp}${apiSecret}`;
  const signature = crypto.createHash("sha1").update(signatureBase).digest("hex");
  const formData = new FormData();

  formData.set("file", imageBase64);
  formData.set("api_key", apiKey);
  formData.set("timestamp", String(timestamp));
  formData.set("signature", signature);
  formData.set("folder", folder);

  const request = await fetch(`https://api.cloudinary.com/v1_1/${cloudName}/image/upload`, {
    method: "POST",
    body: formData,
  });

  const payload = await request.json();

  if (!request.ok) {
    throw new Error(payload?.error?.message || "Cloudinary upload bajarilmadi");
  }

  return payload.secure_url;
}

async function resolveImageUrl({ imageUrl, imageBase64, type, title }) {
  if (imageBase64) {
    return uploadToCloudinary(imageBase64, `gisht-platform/${type || "content"}`);
  }

  if (imageUrl) {
    return safeString(imageUrl, 4000);
  }

  if (type === "product") {
    return makePlaceholderDataUrl(title || "Mahsulot", "#fcd5b4", "#9a3412");
  }
  if (type === "news") {
    return makePlaceholderDataUrl(title || "Yangilik", "#fecaca", "#9f1239");
  }
  return makePlaceholderDataUrl(title || "Blog", "#bfdbfe", "#1d4ed8");
}

async function enrichTasks(tasks) {
  const userIds = new Set();
  for (const task of tasks) {
    if (task.createdBy) {
      userIds.add(normalizeIdString(task.createdBy));
    }
    if (task.acceptedBy) {
      userIds.add(normalizeIdString(task.acceptedBy));
    }
    if (task.completedBy) {
      userIds.add(normalizeIdString(task.completedBy));
    }
  }

  const financeSettings = await getFinanceSettings();
  const paymentTotals = await getTaskPaymentTotalsMap(tasks.map((task) => task._id));
  const objectIds = [...userIds].filter(Boolean).map((id) => new ObjectId(id));
  const users = objectIds.length
    ? await collections.users.find({ _id: { $in: objectIds } }).toArray()
    : [];
  const userMap = new Map(users.map((user) => [normalizeIdString(user._id), serializeUser(user)]));
  return tasks.map((task) => serializeTask({
    ...task,
    ...buildTaskPaymentSnapshot(task, paymentTotals.get(normalizeIdString(task._id)) || 0, financeSettings),
  }, userMap));
}

async function getOverview() {
  const today = getYmd();
  const [usersCount, activeUsersCount, contentsCount, taskCount, doneTodayCount] = await Promise.all([
    collections.users.countDocuments({}),
    collections.users.countDocuments({ isActive: true }),
    collections.contents.countDocuments({ isPublished: true }),
    collections.tasks.countDocuments({}),
    collections.tasks.countDocuments({ status: "done", scheduledDate: today }),
  ]);

  return {
    usersCount,
    activeUsersCount,
    contentsCount,
    taskCount,
    doneTodayCount,
  };
}

async function buildHomePayload() {
  const [products, news, blogs, teamSize, completedProduction, completedDelivery] = await Promise.all([
    collections.contents.find({ type: "product", isPublished: true }).sort({ createdAt: -1 }).limit(3).toArray(),
    collections.contents.find({ type: "news", isPublished: true }).sort({ createdAt: -1 }).limit(3).toArray(),
    collections.contents.find({ type: "blog", isPublished: true }).sort({ createdAt: -1 }).limit(3).toArray(),
    collections.users.countDocuments({ isActive: true }),
    collections.tasks.countDocuments({ type: "production", status: "done" }),
    collections.tasks.countDocuments({ type: "delivery", status: "done" }),
  ]);

  return {
    stats: {
      teamSize,
      completedProduction,
      completedDelivery,
      publishedProducts: products.length,
    },
    featured: {
      products: products.map(serializeContent),
      news: news.map(serializeContent),
      blog: blogs.map(serializeContent),
    },
  };
}

function buildTaskPaymentSnapshot(task, paidAmount = 0, financeSettings = null) {
  const quantity = Math.max(0, Math.round(parseNumber(task.quantity, 0)));
  const unitPrice = roundMoney(
    task.type === "delivery"
      ? (typeof task.unitPrice !== "undefined" ? task.unitPrice : financeSettings?.salePricePerBrick || 0)
      : 0,
  );
  const orderTotal = task.type === "delivery" ? roundMoney(quantity * unitPrice) : 0;
  const normalizedPaidAmount = task.type === "delivery" ? Math.max(0, roundMoney(paidAmount || 0)) : 0;
  const remainingAmount = task.type === "delivery"
    ? roundMoney(Math.max(0, orderTotal - normalizedPaidAmount))
    : 0;
  let paymentStatus = "not_applicable";

  if (task.type === "delivery") {
    if (remainingAmount <= 0 && orderTotal > 0) {
      paymentStatus = "paid";
    } else if (normalizedPaidAmount > 0) {
      paymentStatus = "partial";
    } else {
      paymentStatus = "unpaid";
    }
  }

  return {
    unitPrice,
    orderTotal,
    paidAmount: normalizedPaidAmount,
    remainingAmount,
    paymentStatus,
  };
}

async function getTaskPaymentTotalsMap(taskIds = []) {
  const uniqueIds = [...new Set(taskIds.map((item) => normalizeIdString(item)).filter(Boolean))];
  const objectIds = uniqueIds.filter((id) => ObjectId.isValid(id)).map((id) => new ObjectId(id));
  const payments = objectIds.length
    ? await collections.customerPayments.find({ taskId: { $in: objectIds } }).toArray()
    : [];
  const totals = new Map();

  for (const payment of payments) {
    const key = normalizeIdString(payment.taskId);
    if (!key) {
      continue;
    }
    totals.set(key, roundMoney((totals.get(key) || 0) + roundMoney(payment.amount || 0)));
  }

  return totals;
}

function normalizeFinanceSettings(input = {}) {
  const legacyLaborCostPerBrick = Math.max(0, roundMoney(input.laborCostPerBrick || 0));
  const rateInput = {
    ...getDefaultWorkRates(),
    ...(isPlainObject(input.workRates) ? input.workRates : {}),
  };
  for (const workType of WORK_TYPE_KEYS) {
    if (typeof input[workType] !== "undefined") {
      rateInput[workType] = input[workType];
    }
  }
  if (!isPlainObject(input.workRates) && legacyLaborCostPerBrick > 0 && WORK_TYPE_KEYS.every((key) => !rateInput[key])) {
    rateInput.parmofka = legacyLaborCostPerBrick;
  }

  const workRates = normalizeWorkRates(rateInput);
  const rawMaterialCostPerBrick = roundMoney(input.rawMaterialCostPerBrick || 0);
  const laborCostPerBrick = roundMoney(Object.values(workRates).reduce((sum, value) => sum + value, 0));
  const energyCostPerBrick = roundMoney(input.energyCostPerBrick || 0);
  const transportCostPerBrick = roundMoney(input.transportCostPerBrick || 0);
  const otherCostPerBrick = roundMoney(input.otherCostPerBrick || 0);
  const salePricePerBrick = roundMoney(input.salePricePerBrick || 0);
  const nonLaborCostPerBrick = roundMoney(
    rawMaterialCostPerBrick +
      energyCostPerBrick +
      transportCostPerBrick +
      otherCostPerBrick,
  );
  const totalCostPerBrick = roundMoney(
    nonLaborCostPerBrick + laborCostPerBrick,
  );

  return {
    workRates,
    workTypes: WORK_TYPES.map((item) => ({ ...item, rate: workRates[item.key] || 0 })),
    rawMaterialCostPerBrick,
    laborCostPerBrick,
    energyCostPerBrick,
    transportCostPerBrick,
    otherCostPerBrick,
    salePricePerBrick,
    nonLaborCostPerBrick,
    totalCostPerBrick,
    profitPerBrick: roundMoney(salePricePerBrick - totalCostPerBrick),
  };
}

function normalizeRole(value, fallback = "worker") {
  const role = safeString(value, 20).toLowerCase();
  return ["admin", "organizer", "worker"].includes(role) ? role : fallback;
}

function defaultPositionTitleForRole(role) {
  const normalizedRole = normalizeRole(role, "worker");
  if (normalizedRole === "organizer") {
    return "Organizer";
  }
  if (normalizedRole === "admin") {
    return "Admin";
  }
  return "Ishchi";
}

function normalizePositionTitle(role, value) {
  return safeString(value, 80) || defaultPositionTitleForRole(role);
}

function buildEmptyFinancePeriods() {
  return Object.fromEntries(
    Object.entries(getCurrentPeriodRanges()).map(([key, period]) => [
      key,
      {
        ...period,
        ordersCount: 0,
        bricksCount: 0,
        revenue: 0,
        collectedCash: 0,
        receivableAmount: 0,
        nonLaborExpense: 0,
        pieceworkExpense: 0,
        brickExpense: 0,
        payrollExpense: 0,
        totalExpense: 0,
        grossProfit: 0,
        netProfit: 0,
      },
    ]),
  );
}

function buildOverviewFallback() {
  return {
    usersCount: 0,
    activeUsersCount: 0,
    contentsCount: 0,
    taskCount: 0,
    doneTodayCount: 0,
    todayTasks: 0,
    myAssigned: 0,
    unreadNotifications: 0,
    currentPayrollAmount: 0,
    currentPayrollStatus: "scheduled",
  };
}

async function buildFinanceDashboardSafe() {
  try {
    return await buildFinanceDashboard();
  } catch (error) {
    console.error("Finance dashboard xatosi:", error);
    let settings = normalizeFinanceSettings({});

    try {
      settings = await getFinanceSettings();
    } catch (settingsError) {
      console.error("Finance settings fallback xatosi:", settingsError);
    }

    return {
      settings,
      periods: buildEmptyFinancePeriods(),
      recentOrders: [],
      payroll: [],
      workerBalances: [],
      customerAccounts: [],
      recentPayments: [],
      recentWorkLogs: [],
      recentTransactions: [],
    };
  }
}

async function getSettingValue(key, fallbackValue = null) {
  const document = await collections.settings.findOne({ key });
  return document?.value || fallbackValue;
}

async function setSettingValue(key, value, userId = null) {
  const existing = await collections.settings.findOne({ key });
  const payload = {
    key,
    value,
    updatedAt: new Date(),
    updatedBy: userId || existing?.updatedBy || null,
  };

  if (existing) {
    await collections.settings.updateOne({ _id: existing._id }, { $set: payload });
    return { ...existing, ...payload };
  }

  const document = {
    ...payload,
    createdAt: new Date(),
  };
  const result = await collections.settings.insertOne(document);
  return { ...document, _id: result.insertedId };
}

async function getFinanceSettings() {
  return normalizeFinanceSettings(await getSettingValue("finance", {}));
}

async function updateFinanceSettings(input, userId) {
  const normalized = normalizeFinanceSettings(input);
  await setSettingValue("finance", normalized, userId);
  return normalized;
}

async function getCameraSystemSettings() {
  const system = await getSettingValue("cameraSystem", null);
  if (system) {
    return normalizeCameraSystemSettings(system);
  }

  const legacy = await getSettingValue("camera", null);
  const normalizedLegacy = normalizeCameraSettings(legacy || {});
  const hasLegacyConfig = Boolean(
    normalizedLegacy.snapshotUrl ||
      normalizedLegacy.streamUrl ||
      normalizedLegacy.enabled,
  );

  if (hasLegacyConfig) {
    return {
      monitors: [
        normalizeCameraMonitor({
          ...normalizedLegacy,
          name: "Asosiy kamera",
          areaName: `${workTypeLabel(normalizedLegacy.workType) || "Ish"} liniyasi`,
        }),
      ],
    };
  }

  return { monitors: [] };
}

async function saveCameraSystemSettings(input, userId) {
  const normalized = normalizeCameraSystemSettings(input);
  await setSettingValue("cameraSystem", normalized, userId);
  return normalized;
}

async function listWorkersForCameraMonitor(monitor) {
  const workerIds = normalizeCameraWorkerIds(monitor.workerIds);
  if (!workerIds.length) {
    return [];
  }
  if (workerIds.some((item) => !ObjectId.isValid(item))) {
    return [];
  }

  return collections.users.find({
    _id: { $in: workerIds.map((item) => new ObjectId(item)) },
    role: "worker",
    isActive: true,
  }).toArray();
}

async function validateCameraMonitorConfig(monitor, fallbackMonitor = {}) {
  const normalized = normalizeCameraMonitor(monitor, fallbackMonitor);

  if (!normalized.name) {
    throw new Error("Kamera nomi majburiy.");
  }
  if (!normalized.areaName) {
    throw new Error("Zona nomi majburiy.");
  }
  if (!normalized.snapshotUrl && !normalized.streamUrl) {
    throw new Error("Snapshot yoki RTSP/HTTP stream manzili kiritilishi kerak.");
  }
  if (normalized.streamMode === "rtsp" && !normalized.streamUrl) {
    throw new Error("RTSP rejimida `streamUrl` majburiy.");
  }
  if (normalized.autoSyncWorkLog && !normalized.workerIds.length) {
    throw new Error("Auto work log uchun kameraga 1-10 ta ishchi biriktiring.");
  }

  const workers = await listWorkersForCameraMonitor(normalized);
  if (normalized.workerIds.length && workers.length !== normalized.workerIds.length) {
    throw new Error("Kamera uchun tanlangan ishchilardan biri topilmadi yoki faol emas.");
  }
  const mismatch = workers.find((item) => normalizeWorkType(item.assignedWorkType, "") !== normalized.workType);
  if (mismatch) {
    throw new Error(`${mismatch.fullName} ga ${workTypeLabel(normalized.workType)} emas, boshqa tur biriktirilgan.`);
  }

  return normalized;
}

async function createCameraMonitor(input, userId) {
  const system = await getCameraSystemSettings();
  const normalized = await validateCameraMonitorConfig(input, defaultCameraMonitor(system.monitors.length + 1));
  const nextSystem = {
    monitors: [...system.monitors, normalized],
  };
  await saveCameraSystemSettings(nextSystem, userId);
  return normalized;
}

async function updateCameraMonitor(id, input, userId) {
  const system = await getCameraSystemSettings();
  const current = system.monitors.find((item) => item.id === id);
  if (!current) {
    throw new Error("Kamera topilmadi.");
  }
  const normalized = await validateCameraMonitorConfig({ ...current, ...input, id }, current);
  const nextSystem = {
    monitors: system.monitors.map((item) => (item.id === id ? normalized : item)),
  };
  await saveCameraSystemSettings(nextSystem, userId);
  return normalized;
}

async function deleteCameraMonitor(id, userId) {
  const system = await getCameraSystemSettings();
  const current = system.monitors.find((item) => item.id === id);
  if (!current) {
    throw new Error("Kamera topilmadi.");
  }
  const nextSystem = {
    monitors: system.monitors.filter((item) => item.id !== id),
  };
  await saveCameraSystemSettings(nextSystem, userId);
  return current;
}

async function getCameraSettings() {
  const system = await getCameraSystemSettings();
  return system.monitors[0] || normalizeCameraMonitor(defaultCameraMonitor(1));
}

async function updateCameraSettings(input, userId) {
  const system = await getCameraSystemSettings();
  if (system.monitors[0]) {
    return updateCameraMonitor(system.monitors[0].id, input, userId);
  }
  return createCameraMonitor({
    name: "Asosiy kamera",
    areaName: `${workTypeLabel(input.workType) || "Ish"} liniyasi`,
    ...input,
  }, userId);
}

function resolveCameraTargetUrl(settings, preferSnapshot = true) {
  const candidates = preferSnapshot
    ? [settings.snapshotUrl, settings.streamUrl]
    : [settings.streamUrl, settings.snapshotUrl];

  for (const candidate of candidates) {
    const raw = safeString(candidate, 4000);
    if (!raw) {
      continue;
    }
    try {
      const parsed = new URL(raw);
      if (settings.authType === "query" && settings.apiToken) {
        parsed.searchParams.set(settings.tokenQueryKey || "token", settings.apiToken);
      }
      if (settings.authType === "basic" && settings.username && !parsed.username) {
        parsed.username = settings.username;
        parsed.password = settings.password || "";
      }
      return parsed;
    } catch {
      continue;
    }
  }
  return null;
}

function cameraRequestHeaders(settings) {
  if (settings.authType === "bearer" && settings.apiToken) {
    return { Authorization: `Bearer ${settings.apiToken}` };
  }
  if (settings.authType === "basic" && settings.username) {
    const token = Buffer.from(`${settings.username}:${settings.password || ""}`).toString("base64");
    return { Authorization: `Basic ${token}` };
  }
  return {};
}

function probeTcpPort(host, port, timeoutMs = 2500) {
  return new Promise((resolve) => {
    const socket = net.createConnection({ host, port });
    let settled = false;
    const finish = (result) => {
      if (settled) {
        return;
      }
      settled = true;
      socket.destroy();
      resolve(result);
    };
    socket.setTimeout(timeoutMs);
    socket.once("connect", () => finish(true));
    socket.once("timeout", () => finish(false));
    socket.once("error", () => finish(false));
  });
}

async function extractJpegFrameFromMultipart(response, controller) {
  if (!response.body || typeof response.body.getReader !== "function") {
    throw new Error("MJPEG oqimini o'qib bo'lmadi.");
  }

  const reader = response.body.getReader();
  let buffer = Buffer.alloc(0);
  let totalBytes = 0;
  const maxBytes = 6 * 1024 * 1024;
  const jpegStart = Buffer.from([0xff, 0xd8]);
  const jpegEnd = Buffer.from([0xff, 0xd9]);

  try {
    while (totalBytes < maxBytes) {
      const { done, value } = await reader.read();
      if (done) {
        break;
      }
      const chunk = Buffer.from(value);
      totalBytes += chunk.length;
      buffer = buffer.length ? Buffer.concat([buffer, chunk]) : chunk;

      const start = buffer.indexOf(jpegStart);
      if (start !== -1) {
        const end = buffer.indexOf(jpegEnd, start + 2);
        if (end !== -1) {
          return buffer.subarray(start, end + 2);
        }
        if (start > 0) {
          buffer = buffer.subarray(start);
        }
      } else if (buffer.length > 256 * 1024) {
        buffer = buffer.subarray(buffer.length - 256 * 1024);
      }
    }
  } finally {
    controller.abort();
    reader.releaseLock();
  }

  throw new Error("MJPEG streamdan JPEG frame olinmadi.");
}

async function captureRtspFrame(rtspUrl, settings) {
  let rtspTarget;
  try {
    rtspTarget = new URL(rtspUrl);
  } catch {
    rtspTarget = null;
  }

  if (rtspTarget?.hostname) {
    const port = Number(rtspTarget.port || 554);
    const reachable = await probeTcpPort(rtspTarget.hostname, port);
    if (!reachable) {
      throw new Error(`RTSP port ulanmayapti (${rtspTarget.hostname}:${port}). Stream manzili noto'g'ri yoki port yopiq.`);
    }
  }

  return new Promise((resolve, reject) => {
    const args = [
      "-loglevel",
      "error",
      "-rtsp_transport",
      settings.rtspTransport || "tcp",
      "-i",
      rtspUrl,
      "-frames:v",
      "1",
      "-f",
      "image2pipe",
      "-vcodec",
      "mjpeg",
      "pipe:1",
    ];
    const child = spawn(settings.ffmpegPath || "ffmpeg", args, {
      stdio: ["ignore", "pipe", "pipe"],
      windowsHide: true,
    });
    const stdoutChunks = [];
    const stderrChunks = [];
    let settled = false;
    const timeout = setTimeout(() => {
      if (!settled) {
        settled = true;
        child.kill("SIGKILL");
        reject(new Error("RTSP frame olish vaqti tugadi. Snapshot URL kiriting yoki ffmpeg holatini tekshiring."));
      }
    }, 10_000);

    child.stdout.on("data", (chunk) => stdoutChunks.push(chunk));
    child.stderr.on("data", (chunk) => stderrChunks.push(chunk));
    child.on("error", (error) => {
      clearTimeout(timeout);
      if (settled) {
        return;
      }
      settled = true;
      reject(new Error(
        error.code === "ENOENT"
          ? "RTSP frame uchun ffmpeg topilmadi. `snapshotUrl` kiriting yoki ffmpeg o'rnating."
          : `RTSP frame xatosi: ${error.message}`,
      ));
    });
    child.on("close", (code) => {
      clearTimeout(timeout);
      if (settled) {
        return;
      }
      settled = true;
      const buffer = Buffer.concat(stdoutChunks);
      if (code !== 0 || !buffer.length) {
        const stderr = Buffer.concat(stderrChunks).toString("utf-8").trim();
        reject(new Error(stderr || "RTSP oqimidan frame olinmadi."));
        return;
      }
      resolve({ buffer, contentType: "image/jpeg" });
    });
  });
}

async function fetchCameraFrame(settings) {
  const preferSnapshot = settings.streamMode !== "rtsp";
  const targetUrl = resolveCameraTargetUrl(settings, preferSnapshot);

  if (!targetUrl) {
    throw new Error("Kamera snapshot yoki stream manzili kiritilmagan.");
  }

  if (targetUrl.protocol === "rtsp:") {
    return captureRtspFrame(targetUrl.toString(), settings);
  }

  if (!["http:", "https:"].includes(targetUrl.protocol)) {
    throw new Error("Kamera manzili faqat HTTP(S) snapshot yoki RTSP bo'lishi kerak.");
  }

  const controller = new AbortController();
  const timeout = setTimeout(() => controller.abort(), 8000);
  let response;
  try {
    response = await fetch(targetUrl, {
      headers: cameraRequestHeaders(settings),
      signal: controller.signal,
    });
  } catch (error) {
    throw new Error(error.name === "AbortError" ? "Kamera javobi juda sekin bo'ldi." : error.message);
  }

  if (!response.ok) {
    clearTimeout(timeout);
    throw new Error(`Kamera frame olinmadi (${response.status}).`);
  }

  const contentType = response.headers.get("content-type") || "image/jpeg";
  if (contentType.includes("multipart/")) {
    try {
      const buffer = await extractJpegFrameFromMultipart(response, controller);
      clearTimeout(timeout);
      return {
        buffer,
        contentType: "image/jpeg",
      };
    } catch (error) {
      clearTimeout(timeout);
      throw error;
    }
  }

  try {
    return {
      buffer: Buffer.from(await response.arrayBuffer()),
      contentType,
    };
  } finally {
    clearTimeout(timeout);
  }
}

async function processCameraFrameBuffer(buffer) {
  const pipeline = sharp(buffer, { failOn: "none" }).rotate();
  const metadata = await pipeline.metadata();
  const targetWidth = Math.max(120, Math.min(480, Number(metadata.width || 420)));
  const { data, info } = await pipeline
    .resize({
      width: targetWidth,
      withoutEnlargement: true,
      fit: "inside",
    })
    .greyscale()
    .raw()
    .toBuffer({ resolveWithObject: true });

  return {
    gray: data,
    width: info.width,
    height: info.height,
  };
}

async function renderDemoCameraFrameBuffer() {
  const width = 640;
  const height = 360;
  const positions = [0.78, 0.71, 0.64, 0.57, 0.5, 0.43, 0.36, 0.29, 0.22];
  const index = demoCameraState.requestCount % positions.length;
  demoCameraState.requestCount += 1;
  const barWidth = 58;
  const barHeight = 126;
  const left = Math.max(18, Math.min(width - barWidth - 18, Math.round((width - barWidth) * positions[index])));
  const top = Math.round((height - barHeight) / 2);

  return sharp({
    create: {
      width,
      height,
      channels: 3,
      background: { r: 214, g: 214, b: 214 },
    },
  })
    .composite([
      {
        input: await sharp({
          create: {
            width: width - 70,
            height: 150,
            channels: 3,
            background: { r: 165, g: 165, b: 165 },
          },
        }).png().toBuffer(),
        left: 35,
        top: Math.round((height - 150) / 2),
      },
      {
        input: await sharp({
          create: {
            width: barWidth,
            height: barHeight,
            channels: 3,
            background: { r: 31, g: 41, b: 55 },
          },
        }).png().toBuffer(),
        left,
        top,
      },
    ])
    .jpeg({ quality: 86 })
    .toBuffer();
}

function cameraLinePoints(width, height, settings) {
  return {
    x1: Number(settings.lineStartX || 0) * width,
    y1: Number(settings.lineStartY || 0) * height,
    x2: Number(settings.lineEndX || 1) * width,
    y2: Number(settings.lineEndY || 0) * height,
  };
}

function cameraSignedLineSide(x, y, line) {
  return ((line.x2 - line.x1) * (y - line.y1)) - ((line.y2 - line.y1) * (x - line.x1));
}

function cameraDistanceToSegment(x, y, line) {
  const dx = line.x2 - line.x1;
  const dy = line.y2 - line.y1;
  const lengthSquared = dx * dx + dy * dy || 1;
  let t = ((x - line.x1) * dx + (y - line.y1) * dy) / lengthSquared;
  t = Math.max(0, Math.min(1, t));
  const px = line.x1 + t * dx;
  const py = line.y1 + t * dy;
  return Math.hypot(x - px, y - py);
}

function collectCameraDetections(gray, previousGray, width, height, settings) {
  const threshold = Number(settings.motionThreshold || 28);
  const minBlobArea = Number(settings.minBlobArea || 140);
  const maxBlobArea = Number(settings.maxBlobArea || 12000);
  const line = cameraLinePoints(width, height, settings);
  const bandWidth = Math.max(12, Math.round(Number(settings.trackerDistancePx || 60) * 0.7));
  const binary = new Uint8Array(width * height);

  for (let y = 1; y < height - 1; y += 1) {
    for (let x = 1; x < width - 1; x += 1) {
      const index = y * width + x;
      if (Math.abs(gray[index] - previousGray[index]) < threshold) {
        continue;
      }
      if (cameraDistanceToSegment(x, y, line) > bandWidth) {
        continue;
      }
      binary[index] = 1;
    }
  }

  const cleaned = new Uint8Array(binary.length);
  for (let y = 1; y < height - 1; y += 1) {
    for (let x = 1; x < width - 1; x += 1) {
      const index = y * width + x;
      if (!binary[index]) {
        continue;
      }
      let neighbors = 0;
      for (let yy = -1; yy <= 1; yy += 1) {
        for (let xx = -1; xx <= 1; xx += 1) {
          if (binary[(y + yy) * width + (x + xx)]) {
            neighbors += 1;
          }
        }
      }
      if (neighbors >= 4) {
        cleaned[index] = 1;
      }
    }
  }

  const visited = new Uint8Array(cleaned.length);
  const queue = new Uint32Array(cleaned.length);
  const detections = [];

  for (let y = 1; y < height - 1; y += 1) {
    for (let x = 1; x < width - 1; x += 1) {
      const start = y * width + x;
      if (!cleaned[start] || visited[start]) {
        continue;
      }
      let head = 0;
      let tail = 0;
      queue[tail++] = start;
      visited[start] = 1;
      let area = 0;
      let sumX = 0;
      let sumY = 0;
      let minX = x;
      let minY = y;
      let maxX = x;
      let maxY = y;

      while (head < tail) {
        const index = queue[head++];
        const qx = index % width;
        const qy = Math.floor(index / width);
        area += 1;
        sumX += qx;
        sumY += qy;
        if (qx < minX) minX = qx;
        if (qy < minY) minY = qy;
        if (qx > maxX) maxX = qx;
        if (qy > maxY) maxY = qy;

        for (let yy = -1; yy <= 1; yy += 1) {
          for (let xx = -1; xx <= 1; xx += 1) {
            const nx = qx + xx;
            const ny = qy + yy;
            if (nx < 1 || ny < 1 || nx >= width - 1 || ny >= height - 1) {
              continue;
            }
            const neighbor = ny * width + nx;
            if (cleaned[neighbor] && !visited[neighbor]) {
              visited[neighbor] = 1;
              queue[tail++] = neighbor;
            }
          }
        }
      }

      if (area >= minBlobArea && area <= maxBlobArea) {
        detections.push({
          area,
          x: minX,
          y: minY,
          width: Math.max(1, maxX - minX + 1),
          height: Math.max(1, maxY - minY + 1),
          cx: sumX / area,
          cy: sumY / area,
        });
      }
    }
  }

  return { detections, line };
}

function cameraCrossingMatchesDirection(previousSide, currentSide, direction) {
  if (Math.abs(previousSide) <= 2 || Math.abs(currentSide) <= 2) {
    return false;
  }
  if (Math.sign(previousSide) === Math.sign(currentSide)) {
    return false;
  }
  if (direction === "negative_to_positive") {
    return previousSide < 0 && currentSide > 0;
  }
  if (direction === "positive_to_negative") {
    return previousSide > 0 && currentSide < 0;
  }
  return true;
}

function updateCameraTracks(runtime, detections, line) {
  const now = Date.now();
  const maxDistance = Number(runtime.monitor.trackerDistancePx || 60);
  const matchedTrackIds = new Set();
  let increment = 0;

  detections.forEach((detection) => {
    let bestTrack = null;
    let bestDistance = Number.POSITIVE_INFINITY;

    runtime.tracks.forEach((track) => {
      if (matchedTrackIds.has(track.id)) {
        return;
      }
      const distance = Math.hypot(track.cx - detection.cx, track.cy - detection.cy);
      if (distance < bestDistance && distance <= maxDistance) {
        bestTrack = track;
        bestDistance = distance;
      }
    });

    const currentSide = cameraSignedLineSide(detection.cx, detection.cy, line);
    if (!bestTrack) {
      bestTrack = {
        id: runtime.nextTrackId++,
        cx: detection.cx,
        cy: detection.cy,
        lastSide: currentSide,
        lastSeenAt: now,
        countedAt: 0,
      };
      runtime.tracks.push(bestTrack);
    } else {
      const previousSide = bestTrack.lastSide;
      if (
        cameraCrossingMatchesDirection(previousSide, currentSide, runtime.monitor.countDirection || "both") &&
        now - bestTrack.countedAt > 600
      ) {
        increment += 1;
        bestTrack.countedAt = now;
      }
      bestTrack.cx = detection.cx;
      bestTrack.cy = detection.cy;
      bestTrack.lastSide = currentSide;
      bestTrack.lastSeenAt = now;
    }

    matchedTrackIds.add(bestTrack.id);
  });

  runtime.tracks = runtime.tracks.filter((track) => now - track.lastSeenAt < 3000);
  return increment;
}

function compareMonthKeys(left, right) {
  const [leftYear, leftMonth] = String(left || "0000-00").split("-").map(Number);
  const [rightYear, rightMonth] = String(right || "0000-00").split("-").map(Number);
  return (leftYear * 12 + leftMonth) - (rightYear * 12 + rightMonth);
}

function listMonthKeysBetween(startMonthKey, endMonthKey) {
  if (!startMonthKey || !endMonthKey || compareMonthKeys(startMonthKey, endMonthKey) > 0) {
    return [];
  }

  const [startYear, startMonth] = String(startMonthKey).split("-").map(Number);
  const [endYear, endMonth] = String(endMonthKey).split("-").map(Number);
  const monthKeys = [];
  let year = startYear;
  let month = startMonth;

  while (year < endYear || (year === endYear && month <= endMonth)) {
    monthKeys.push(`${year}-${String(month).padStart(2, "0")}`);
    month += 1;
    if (month > 12) {
      year += 1;
      month = 1;
    }
  }

  return monthKeys;
}

async function resolveCameraMonitorWorkers(monitor) {
  const workers = await listWorkersForCameraMonitor(monitor);
  if (!monitor.workerIds.length) {
    return { workers, warning: "Ishchilar hali biriktirilmagan." };
  }
  if (workers.length !== monitor.workerIds.length) {
    return { workers, warning: "Biriktirilgan ishchilardan biri topilmadi yoki faol emas." };
  }
  const mismatch = workers.find((item) => normalizeWorkType(item.assignedWorkType, "") !== monitor.workType);
  if (mismatch) {
    return {
      workers,
      warning: `${mismatch.fullName} uchun ${workTypeLabel(monitor.workType)} turi biriktirilmagan.`,
    };
  }
  return { workers, warning: "" };
}

async function getCameraCountRecord(monitorId, date = getYmd()) {
  return collections.cameraCounts.findOne({ monitorId, date });
}

async function setCameraCountRecord(payload) {
  const existing = await collections.cameraCounts.findOne({
    monitorId: payload.monitorId,
    date: payload.date,
  });

  if (existing) {
    await collections.cameraCounts.updateOne({ _id: existing._id }, { $set: payload });
    return { ...existing, ...payload };
  }

  const result = await collections.cameraCounts.insertOne({
    ...payload,
    createdAt: payload.createdAt || new Date(),
  });
  return { ...payload, _id: result.insertedId };
}

async function syncCameraWorkLogFromMonitor(monitor, date, quantity) {
  if (!monitor.autoSyncWorkLog) {
    return { workLogId: "", warning: "" };
  }

  const { workers, warning } = await resolveCameraMonitorWorkers(monitor);
  if (!workers.length) {
    return { workLogId: "", warning: warning || "Ishchi biriktirilmagan." };
  }
  if (warning) {
    return { workLogId: "", warning };
  }

  const financeSettings = await getFinanceSettings();
  const ratePerBrick = roundMoney(financeSettings.workRates?.[monitor.workType] || 0);
  if (ratePerBrick <= 0) {
    return { workLogId: "", warning: `${workTypeLabel(monitor.workType)} uchun stavka kiritilmagan.` };
  }

  const totalAmount = roundMoney(quantity * ratePerBrick);
  const shareAmount = workers.length ? roundMoney(totalAmount / workers.length) : 0;
  const now = new Date();
  const existing = await collections.workLogs.findOne({
    cameraMonitorId: monitor.id,
    date,
  });

  if (quantity <= 0 && !existing) {
    return { workLogId: "", warning: "" };
  }

  const payload = {
    date,
    workType: monitor.workType,
    quantity,
    ratePerBrick,
    totalAmount,
    shareAmount,
    workerIds: workers.map((item) => toStoredId(item._id)).filter(Boolean),
    notes: safeString(
      monitor.notes || `Kamera nazorati: ${monitor.name} (${monitor.areaName})`,
      500,
    ),
    source: "camera",
    cameraMonitorId: monitor.id,
    cameraMonitorName: monitor.name,
    createdBy: null,
    updatedAt: now,
  };

  if (existing) {
    await collections.workLogs.updateOne({ _id: existing._id }, { $set: payload });
    return { workLogId: normalizeIdString(existing._id), warning: "" };
  }

  const result = await collections.workLogs.insertOne({
    ...payload,
    createdAt: now,
  });
  return { workLogId: normalizeIdString(result.insertedId), warning: "" };
}

async function syncAllCameraWorkLogsForDate(date = getYmd()) {
  const system = await getCameraSystemSettings();
  await Promise.all(
    system.monitors.map(async (monitor) => {
      const counter = await getCameraCountRecord(monitor.id, date);
      if (!counter) {
        return;
      }
      await syncCameraWorkLogFromMonitor(monitor, date, Math.max(0, Math.round(counter.quantity || 0)));
    }),
  );
}

function createCameraRuntime(monitor, counter = null) {
  return {
    monitor,
    active: Boolean(monitor.enabled),
    timer: null,
    previousGray: null,
    tracks: [],
    nextTrackId: 1,
    dateKey: counter?.date || getYmd(),
    count: Math.max(0, Math.round(counter?.quantity || 0)),
    lastFrameAt: counter?.lastFrameAt ? new Date(counter.lastFrameAt) : null,
    lastCountAt: counter?.lastCountAt ? new Date(counter.lastCountAt) : null,
    lastError: counter?.lastError || "",
    lastWarning: counter?.lastWarning || "",
    status: monitor.enabled ? "starting" : "disabled",
    workLogId: counter?.workLogId || "",
    frameWidth: 0,
    frameHeight: 0,
    needsWorkLogRefresh: true,
  };
}

function stopCameraRuntime(runtime, status = "disabled") {
  if (!runtime) {
    return;
  }
  runtime.active = false;
  if (runtime.timer) {
    clearTimeout(runtime.timer);
    runtime.timer = null;
  }
  runtime.status = status;
}

async function persistCameraRuntime(runtime) {
  const now = new Date();
  return setCameraCountRecord({
    monitorId: runtime.monitor.id,
    monitorName: runtime.monitor.name,
    areaName: runtime.monitor.areaName,
    workType: runtime.monitor.workType,
    date: runtime.dateKey || getYmd(),
    quantity: Math.max(0, Math.round(runtime.count || 0)),
    workLogId: runtime.workLogId || "",
    status: runtime.status || "idle",
    lastError: runtime.lastError || "",
    lastWarning: runtime.lastWarning || "",
    lastFrameAt: runtime.lastFrameAt || null,
    lastCountAt: runtime.lastCountAt || null,
    workerIds: runtime.monitor.workerIds || [],
    updatedAt: now,
  });
}

function scheduleCameraRuntime(runtime, delay = null) {
  if (!runtime?.active) {
    return;
  }
  if (runtime.timer) {
    clearTimeout(runtime.timer);
  }
  runtime.timer = setTimeout(() => {
    runCameraRuntime(runtime).catch((error) => {
      runtime.status = "error";
      runtime.lastError = error.message || "Kamera runtime xatosi.";
      persistCameraRuntime(runtime).catch(() => null);
      scheduleCameraRuntime(runtime, runtime.monitor.frameIntervalMs || 1000);
    });
  }, delay ?? runtime.monitor.frameIntervalMs ?? 1000);
}

async function runCameraRuntime(runtime) {
  if (!runtime?.active) {
    return;
  }

  const currentDate = getYmd();
  if (runtime.dateKey !== currentDate) {
    const counter = await getCameraCountRecord(runtime.monitor.id, currentDate);
    runtime.dateKey = currentDate;
    runtime.count = Math.max(0, Math.round(counter?.quantity || 0));
    runtime.workLogId = counter?.workLogId || "";
    runtime.previousGray = null;
    runtime.tracks = [];
    runtime.nextTrackId = 1;
    runtime.needsWorkLogRefresh = true;
  }

  try {
    runtime.status = "capturing";
    const frame = await fetchCameraFrame(runtime.monitor);
    const processed = await processCameraFrameBuffer(frame.buffer);
    runtime.frameWidth = processed.width;
    runtime.frameHeight = processed.height;
    runtime.lastFrameAt = new Date();
    runtime.lastError = "";
    let increment = 0;

    if (runtime.previousGray && runtime.previousGray.length === processed.gray.length) {
      const detectionState = collectCameraDetections(
        processed.gray,
        runtime.previousGray,
        processed.width,
        processed.height,
        runtime.monitor,
      );
      increment = updateCameraTracks(runtime, detectionState.detections, detectionState.line);
    } else {
      runtime.tracks = [];
    }

    runtime.previousGray = processed.gray;

    if (increment > 0) {
      runtime.count = Math.max(0, Math.round(runtime.count + increment));
      runtime.lastCountAt = new Date();
      runtime.needsWorkLogRefresh = true;
    }

    if (runtime.needsWorkLogRefresh) {
      const syncResult = await syncCameraWorkLogFromMonitor(
        runtime.monitor,
        runtime.dateKey,
        Math.max(0, Math.round(runtime.count || 0)),
      );
      runtime.workLogId = syncResult.workLogId || runtime.workLogId || "";
      runtime.lastWarning = syncResult.warning || "";
      runtime.needsWorkLogRefresh = false;
    }

    runtime.status = "running";
    await persistCameraRuntime(runtime);
  } catch (error) {
    runtime.status = "error";
    runtime.lastError = error.message || "Kamera xatosi.";
    await persistCameraRuntime(runtime);
  }

  scheduleCameraRuntime(runtime);
}

async function reloadCameraMonitorService() {
  if (cameraMonitorService.reloading) {
    return cameraMonitorService.reloading;
  }

  cameraMonitorService.reloading = (async () => {
    const system = await getCameraSystemSettings();
    const desiredIds = new Set(system.monitors.map((item) => item.id));

    for (const [id, runtime] of cameraMonitorService.runtimes.entries()) {
      const updatedMonitor = system.monitors.find((item) => item.id === id);
      if (!updatedMonitor || !updatedMonitor.enabled) {
        stopCameraRuntime(runtime, updatedMonitor ? "disabled" : "removed");
        await persistCameraRuntime(runtime).catch(() => null);
        cameraMonitorService.runtimes.delete(id);
      }
    }

    for (const monitor of system.monitors) {
      const counter = await getCameraCountRecord(monitor.id, getYmd());
      if (!monitor.enabled) {
        if (!counter) {
          await setCameraCountRecord({
            monitorId: monitor.id,
            monitorName: monitor.name,
            areaName: monitor.areaName,
            workType: monitor.workType,
            date: getYmd(),
            quantity: 0,
            workLogId: "",
            status: "disabled",
            lastError: "",
            lastWarning: "",
            lastFrameAt: null,
            lastCountAt: null,
            workerIds: monitor.workerIds || [],
            updatedAt: new Date(),
            createdAt: new Date(),
          }).catch(() => null);
        }
        continue;
      }

      let runtime = cameraMonitorService.runtimes.get(monitor.id);
      if (!runtime) {
        runtime = createCameraRuntime(monitor, counter);
        cameraMonitorService.runtimes.set(monitor.id, runtime);
        scheduleCameraRuntime(runtime, 50);
      } else {
        runtime.monitor = monitor;
        runtime.active = true;
        runtime.needsWorkLogRefresh = true;
        runtime.status = runtime.status === "error" ? "starting" : runtime.status;
        scheduleCameraRuntime(runtime, 50);
      }
    }

    for (const id of [...cameraMonitorService.runtimes.keys()]) {
      if (!desiredIds.has(id)) {
        cameraMonitorService.runtimes.delete(id);
      }
    }

    cameraMonitorService.ready = true;
  })().finally(() => {
    cameraMonitorService.reloading = null;
  });

  return cameraMonitorService.reloading;
}

async function stopAllCameraMonitors() {
  for (const runtime of cameraMonitorService.runtimes.values()) {
    stopCameraRuntime(runtime, "stopped");
    await persistCameraRuntime(runtime).catch(() => null);
  }
  cameraMonitorService.runtimes.clear();
}

async function resetCameraCounterForDate(monitorId, date = getYmd()) {
  const runtime = cameraMonitorService.runtimes.get(monitorId);
  const counter = await getCameraCountRecord(monitorId, date);
  if (!counter) {
    return null;
  }

  const payload = {
    ...counter,
    quantity: 0,
    workLogId: "",
    status: runtime?.status || counter.status || "idle",
    lastWarning: "",
    updatedAt: new Date(),
  };
  await setCameraCountRecord(payload);

  if (runtime && runtime.dateKey === date) {
    runtime.count = 0;
    runtime.previousGray = null;
    runtime.tracks = [];
    runtime.nextTrackId = 1;
    runtime.workLogId = "";
    runtime.needsWorkLogRefresh = true;
  }

  const system = await getCameraSystemSettings();
  const monitor = system.monitors.find((item) => item.id === monitorId);
  if (monitor) {
    await syncCameraWorkLogFromMonitor(monitor, date, 0);
  }

  return payload;
}

async function buildCameraMonitorsPayload(date = getYmd()) {
  const system = await getCameraSystemSettings();
  const monitorIds = system.monitors.map((item) => item.id);
  const counters = monitorIds.length
    ? await collections.cameraCounts.find({ monitorId: { $in: monitorIds }, date }).toArray()
    : [];
  const counterMap = new Map(counters.map((item) => [item.monitorId, item]));
  const workerIds = [...new Set(system.monitors.flatMap((item) => item.workerIds || []))];
  const workerMap = await getUserMapByIds(workerIds);

  return system.monitors.map((monitor) => {
    const runtime = cameraMonitorService.runtimes.get(monitor.id);
    const counter = counterMap.get(monitor.id) || null;
    const workers = (monitor.workerIds || []).map((item) => workerMap.get(item)).filter(Boolean);
    return {
      ...monitor,
      workers,
      countToday: Math.max(0, Math.round(runtime?.count ?? counter?.quantity ?? 0)),
      status: runtime?.status || counter?.status || (monitor.enabled ? "idle" : "disabled"),
      lastError: runtime?.lastError || counter?.lastError || "",
      lastWarning: runtime?.lastWarning || counter?.lastWarning || "",
      lastFrameAt: runtime?.lastFrameAt || counter?.lastFrameAt || null,
      lastCountAt: runtime?.lastCountAt || counter?.lastCountAt || null,
      workLogId: runtime?.workLogId || counter?.workLogId || "",
      frameWidth: runtime?.frameWidth || 0,
      frameHeight: runtime?.frameHeight || 0,
    };
  });
}

async function buildProductionSummary(date = getYmd(), viewer = null) {
  const [financeSettings, monitors, workLogs] = await Promise.all([
    getFinanceSettings(),
    buildCameraMonitorsPayload(date),
    collections.workLogs.find({ date }).sort({ createdAt: 1 }).toArray(),
  ]);

  const workerIds = new Set();
  monitors.forEach((monitor) => {
    (monitor.workerIds || []).forEach((item) => workerIds.add(normalizeIdString(item)));
  });
  workLogs.forEach((log) => {
    (Array.isArray(log.workerIds) ? log.workerIds : []).forEach((item) => workerIds.add(normalizeIdString(item)));
  });

  const workerMap = await getUserMapByIds([...workerIds]);
  const byWorkType = new Map(
    WORK_TYPES.map((item) => [item.key, {
      workType: item.key,
      workTypeLabel: item.label,
      ratePerBrick: roundMoney(financeSettings.workRates?.[item.key] || 0),
      cameraQuantity: 0,
      loggedQuantity: 0,
      totalAmount: 0,
      workLogCount: 0,
      monitorCount: 0,
      automated: false,
      taskRequired: false,
      monitors: [],
      workers: new Map(),
    }]),
  );

  const upsertWorker = (summary, userLike, seed = {}) => {
    if (!userLike?.id) {
      return;
    }
    const existing = summary.workers.get(userLike.id) || {
      id: userLike.id,
      fullName: userLike.fullName || "Ishchi",
      assignedWorkType: userLike.assignedWorkType || "",
      assignedWorkTypeLabel: userLike.assignedWorkTypeLabel || "",
      todayAmount: 0,
      todayQuantity: 0,
      workLogCount: 0,
    };
    existing.fullName = existing.fullName || userLike.fullName || "Ishchi";
    existing.assignedWorkType = existing.assignedWorkType || userLike.assignedWorkType || "";
    existing.assignedWorkTypeLabel = existing.assignedWorkTypeLabel || userLike.assignedWorkTypeLabel || "";
    if (seed.todayAmount) {
      existing.todayAmount = roundMoney(existing.todayAmount + seed.todayAmount);
    }
    if (seed.todayQuantity) {
      existing.todayQuantity = Math.max(0, Math.round(existing.todayQuantity + seed.todayQuantity));
    }
    if (seed.workLogCount) {
      existing.workLogCount += seed.workLogCount;
    }
    summary.workers.set(existing.id, existing);
  };

  monitors.forEach((monitor) => {
    const summary = byWorkType.get(monitor.workType);
    if (!summary) {
      return;
    }
    summary.cameraQuantity = Math.max(0, Math.round(summary.cameraQuantity + (monitor.countToday || 0)));
    summary.monitorCount += 1;
    summary.automated = summary.automated || Boolean(monitor.autoSyncWorkLog);
    summary.monitors.push({
      id: monitor.id,
      name: monitor.name,
      areaName: monitor.areaName,
      enabled: Boolean(monitor.enabled),
      status: monitor.status,
      countToday: Math.max(0, Math.round(monitor.countToday || 0)),
      workLogId: monitor.workLogId || "",
      autoSyncWorkLog: Boolean(monitor.autoSyncWorkLog),
      lastError: monitor.lastError || "",
      lastWarning: monitor.lastWarning || "",
    });
    (monitor.workers || []).forEach((worker) => upsertWorker(summary, worker));
  });

  workLogs.forEach((log) => {
    const workType = normalizeWorkType(log.workType, "");
    const summary = byWorkType.get(workType);
    if (!summary) {
      return;
    }
    const quantity = Math.max(0, Math.round(log.quantity || 0));
    const totalAmount = roundMoney(log.totalAmount || 0);
    const shareAmount = roundMoney(log.shareAmount || 0);
    summary.loggedQuantity = Math.max(0, Math.round(summary.loggedQuantity + quantity));
    summary.totalAmount = roundMoney(summary.totalAmount + totalAmount);
    summary.workLogCount += 1;
    (Array.isArray(log.workerIds) ? log.workerIds : []).forEach((workerId) => {
      const workerKey = normalizeIdString(workerId);
      const serialized = workerMap.get(workerKey) || { id: workerKey, fullName: "Ishchi" };
      upsertWorker(summary, serialized, {
        todayAmount: shareAmount,
        todayQuantity: quantity,
        workLogCount: 1,
      });
    });
  });

  let items = [...byWorkType.values()].map((summary) => {
    const workers = [...summary.workers.values()].sort((left, right) => {
      if (right.todayAmount !== left.todayAmount) {
        return right.todayAmount - left.todayAmount;
      }
      return String(left.fullName || "").localeCompare(String(right.fullName || ""));
    });
    return {
      workType: summary.workType,
      workTypeLabel: summary.workTypeLabel,
      ratePerBrick: summary.ratePerBrick,
      cameraQuantity: Math.max(0, Math.round(summary.cameraQuantity)),
      loggedQuantity: Math.max(0, Math.round(summary.loggedQuantity)),
      totalAmount: roundMoney(summary.totalAmount),
      workLogCount: summary.workLogCount,
      monitorCount: summary.monitorCount,
      workerCount: workers.length,
      automated: summary.automated,
      taskRequired: false,
      note: summary.monitorCount
        ? "Bu tur doimiy kamera counti bilan yuradi. Alohida vazifa berish shart emas."
        : "Kamera biriktirilsa bu tur ham avtomatik hisoblanadi.",
      quantityGap: Math.max(0, Math.round(summary.cameraQuantity - summary.loggedQuantity)),
      monitors: summary.monitors,
      workers,
    };
  });

  if (viewer?.role === "worker") {
    const viewerId = normalizeIdString(viewer._id);
    const assignedWorkType = normalizeWorkType(viewer.assignedWorkType, "");
    items = items.filter((item) =>
      item.workType === assignedWorkType ||
      item.workers.some((worker) => worker.id === viewerId),
    );
  }

  items = items.filter((item) => item.monitorCount || item.loggedQuantity || item.workerCount);

  const totals = {
    workTypeCount: items.length,
    monitorCount: items.reduce((sum, item) => sum + item.monitorCount, 0),
    workerCount: [...new Set(items.flatMap((item) => item.workers.map((worker) => worker.id)))].length,
    cameraQuantity: items.reduce((sum, item) => sum + item.cameraQuantity, 0),
    loggedQuantity: items.reduce((sum, item) => sum + item.loggedQuantity, 0),
    totalAmount: roundMoney(items.reduce((sum, item) => sum + item.totalAmount, 0)),
  };

  const mine = viewer ? items.reduce((accumulator, item) => {
    const current = item.workers.find((worker) => worker.id === normalizeIdString(viewer._id));
    if (!current) {
      return accumulator;
    }
    accumulator.todayAmount = roundMoney(accumulator.todayAmount + current.todayAmount);
    accumulator.todayQuantity = Math.max(0, Math.round(accumulator.todayQuantity + current.todayQuantity));
    accumulator.workTypes.push(item.workType);
    return accumulator;
  }, {
    todayAmount: 0,
    todayQuantity: 0,
    workTypes: [],
    assignedWorkType: normalizeWorkType(viewer.assignedWorkType, ""),
  }) : null;

  if (mine) {
    mine.workTypes = [...new Set(mine.workTypes)];
  }

  return {
    date,
    totals,
    items,
    mine,
    note: "Ishlab chiqarish liniyalari kamera counti asosida kunlik avtomatik hisoblanadi.",
  };
}

function buildPayrollIdentifier(userId, monthKey, existingId = "") {
  return existingId || `${userId}:${monthKey}`;
}

function parsePayrollIdentifier(value) {
  const raw = safeString(value, 80);
  if (ObjectId.isValid(raw)) {
    return { kind: "objectId", id: raw };
  }

  const [userId, monthKey] = raw.split(":");
  if (ObjectId.isValid(userId) && /^\d{4}-\d{2}$/.test(monthKey || "")) {
    return { kind: "synthetic", userId, monthKey };
  }

  return null;
}

function paymentStatusFromAmounts(totalAmount, paidAmount) {
  const total = roundMoney(totalAmount || 0);
  const paid = roundMoney(paidAmount || 0);
  if (total <= 0) {
    return "unpaid";
  }
  if (paid >= total) {
    return "paid";
  }
  if (paid > 0) {
    return "partial";
  }
  return "unpaid";
}

async function enrichWorkLogs(records) {
  const userIds = new Set();
  for (const record of records) {
    for (const workerId of record.workerIds || []) {
      userIds.add(normalizeIdString(workerId));
    }
    if (record.createdBy) {
      userIds.add(normalizeIdString(record.createdBy));
    }
  }

  const userMap = await getUserMapByIds([...userIds]);
  return records.map((record) => serializeWorkLog(record, userMap));
}

async function enrichWorkerTransactions(records) {
  const userIds = new Set();
  for (const record of records) {
    if (record.workerId) {
      userIds.add(normalizeIdString(record.workerId));
    }
    if (record.createdBy) {
      userIds.add(normalizeIdString(record.createdBy));
    }
  }

  const userMap = await getUserMapByIds([...userIds]);
  return records.map((record) => serializeWorkerTransaction(record, userMap));
}

async function getDeliveryFinanceEntries(financeSettings = null) {
  const settings = financeSettings || await getFinanceSettings();
  const deliveries = await collections.tasks.find({ type: "delivery" }).toArray();
  const paymentTotals = await getTaskPaymentTotalsMap(deliveries.map((task) => task._id));

  return deliveries.map((task) => {
    const payment = buildTaskPaymentSnapshot(task, paymentTotals.get(normalizeIdString(task._id)) || 0, settings);
    const quantity = Math.max(0, Math.round(parseNumber(task.quantity, 0)));
    const nonLaborExpense = roundMoney(quantity * settings.nonLaborCostPerBrick);
    const pieceworkExpense = roundMoney(quantity * settings.laborCostPerBrick);
    const totalExpense = roundMoney(nonLaborExpense + pieceworkExpense);

    return {
      taskId: normalizeIdString(task._id),
      customerName: task.customerName,
      quantity,
      date: getTaskAccountingDate(task),
      status: task.status,
      unitPrice: payment.unitPrice,
      revenue: payment.orderTotal,
      paidAmount: payment.paidAmount,
      remainingAmount: payment.remainingAmount,
      paymentStatus: payment.paymentStatus,
      nonLaborExpense,
      pieceworkExpense,
      totalExpense,
      profit: roundMoney(payment.orderTotal - totalExpense),
    };
  });
}

function computeMonthlySettlement(user, monthKey, userWorkLogs = [], userTransactions = [], userPayrollMap = new Map()) {
  const createdMonthKey = toMonthKey(user.createdAt || new Date());
  const monthKeys = listMonthKeysBetween(createdMonthKey, monthKey);
  const fallbackDueDate = buildMonthDate(monthKey, clampNumber(user.salaryDayOfMonth || 5, 1, 31, 5));

  if (!monthKeys.length) {
    return {
      id: buildPayrollIdentifier(normalizeIdString(user._id), monthKey),
      monthKey,
      dueDate: fallbackDueDate,
      amount: 0,
      accruedAmount: 0,
      pieceworkAmount: 0,
      baseSalaryAmount: 0,
      bonusAmount: 0,
      advanceAmount: 0,
      openingBalance: 0,
      beforePaymentBalance: 0,
      paidAmount: 0,
      closingBalance: 0,
      payableAmount: 0,
      debtAmount: 0,
      processedQuantity: 0,
      workLogCount: 0,
      status: "settled",
      notes: "",
      paidAt: null,
      user: serializeUser(user),
    };
  }

  let runningBalance = 0;
  let finalSummary = null;

  for (const currentMonthKey of monthKeys) {
    const monthlyLogs = userWorkLogs.filter((item) => safeString(item.date, 7) === currentMonthKey);
    const monthlyTransactions = userTransactions.filter((item) => safeString(item.date, 7) === currentMonthKey);
    const payrollRecord = userPayrollMap.get(currentMonthKey) || null;
    const openingBalance = runningBalance;
    const pieceworkAmount = roundMoney(
      monthlyLogs.reduce((sum, item) => sum + roundMoney(item.shareAmount || 0), 0),
    );
    const processedQuantity = monthlyLogs.reduce(
      (sum, item) => sum + Math.max(0, Math.round(parseNumber(item.quantity, 0))),
      0,
    );
    let bonusAmount = 0;
    let advanceAmount = 0;

    for (const transaction of monthlyTransactions) {
      const amount = roundMoney(transaction.amount || 0);
      if (workerTransactionMeta(transaction.type).effect === "credit") {
        bonusAmount = roundMoney(bonusAmount + amount);
      } else {
        advanceAmount = roundMoney(advanceAmount + amount);
      }
    }

    const baseSalaryAmount = user.role === "worker"
      ? 0
      : compareMonthKeys(currentMonthKey, createdMonthKey) >= 0
        ? roundMoney(user.salaryAmount || 0)
        : 0;
    const accruedAmount = roundMoney(pieceworkAmount + baseSalaryAmount + bonusAmount);
    const beforePaymentBalance = roundMoney(openingBalance + accruedAmount - advanceAmount);
    const paidAmount = payrollRecord?.status === "paid" ? roundMoney(payrollRecord.amount || 0) : 0;
    const closingBalance = roundMoney(beforePaymentBalance - paidAmount);
    const payableAmount = roundMoney(Math.max(0, closingBalance));
    const debtAmount = roundMoney(Math.max(0, -closingBalance));
    const dueDate = buildMonthDate(currentMonthKey, clampNumber(user.salaryDayOfMonth || 5, 1, 31, 5));

    let status = "pending";
    if (debtAmount > 0) {
      status = "debt";
    } else if (payableAmount === 0) {
      status = "paid";
    } else if (paidAmount > 0) {
      status = "partial";
    }

    const summary = {
      id: buildPayrollIdentifier(
        normalizeIdString(user._id),
        currentMonthKey,
        normalizeIdString(payrollRecord?._id) || "",
      ),
      monthKey: currentMonthKey,
      dueDate,
      amount: payableAmount,
      accruedAmount,
      pieceworkAmount,
      baseSalaryAmount,
      bonusAmount,
      advanceAmount,
      openingBalance,
      beforePaymentBalance,
      paidAmount,
      closingBalance,
      payableAmount,
      debtAmount,
      processedQuantity,
      workLogCount: monthlyLogs.length,
      status,
      notes: payrollRecord?.notes || "",
      paidAt: payrollRecord?.paidAt || null,
      user: serializeUser(user),
    };

    runningBalance = closingBalance;
    if (currentMonthKey === monthKey) {
      finalSummary = summary;
    }
  }

  return finalSummary;
}

async function buildPayrollSnapshots({ monthKey = toMonthKey(), users = null } = {}) {
  const targetUsers = users || await collections.users.find({ isActive: true }).sort({ createdAt: 1 }).toArray();
  const objectIds = targetUsers
    .map((user) => user._id)
    .filter(Boolean)
    .map((id) => new ObjectId(normalizeIdString(id)));

  const [workLogs, workerTransactions, payrolls] = await Promise.all([
    objectIds.length ? collections.workLogs.find({ workerIds: { $in: objectIds } }).toArray() : [],
    objectIds.length ? collections.workerTransactions.find({ workerId: { $in: objectIds } }).toArray() : [],
    objectIds.length ? collections.payrolls.find({ userId: { $in: objectIds } }).toArray() : [],
  ]);

  const logsByUser = new Map();
  for (const user of targetUsers) {
    logsByUser.set(normalizeIdString(user._id), []);
  }
  for (const log of workLogs) {
    for (const workerId of log.workerIds || []) {
      const key = normalizeIdString(workerId);
      if (!logsByUser.has(key)) {
        logsByUser.set(key, []);
      }
      logsByUser.get(key).push(log);
    }
  }

  const transactionsByUser = new Map();
  for (const transaction of workerTransactions) {
    const key = normalizeIdString(transaction.workerId);
    if (!key) {
      continue;
    }
    if (!transactionsByUser.has(key)) {
      transactionsByUser.set(key, []);
    }
    transactionsByUser.get(key).push(transaction);
  }

  const payrollsByUser = new Map();
  for (const record of payrolls) {
    const key = normalizeIdString(record.userId);
    if (!key) {
      continue;
    }
    if (!payrollsByUser.has(key)) {
      payrollsByUser.set(key, new Map());
    }
    payrollsByUser.get(key).set(record.monthKey, record);
  }

  return targetUsers.map((user) => computeMonthlySettlement(
    user,
    monthKey,
    logsByUser.get(normalizeIdString(user._id)) || [],
    transactionsByUser.get(normalizeIdString(user._id)) || [],
    payrollsByUser.get(normalizeIdString(user._id)) || new Map(),
  ));
}

async function getPayrollSnapshotForUser(user, monthKey = toMonthKey()) {
  const [snapshot] = await buildPayrollSnapshots({ monthKey, users: [user] });
  return snapshot || computeMonthlySettlement(user, monthKey);
}

function filterWorkerAccountByStatus(item, status) {
  if (status === "debtor") {
    return item.debtAmount > 0;
  }
  if (status === "payable") {
    return item.payableAmount > 0;
  }
  if (status === "settled") {
    return item.payableAmount <= 0 && item.debtAmount <= 0;
  }
  return true;
}

function filterCustomerAccountByStatus(item, status) {
  if (status === "debtor") {
    return item.remainingAmount > 0;
  }
  if (status === "paid") {
    return item.totalAmount > 0 && item.remainingAmount <= 0;
  }
  if (status === "partial") {
    return item.paidAmount > 0 && item.remainingAmount > 0;
  }
  if (status === "unpaid") {
    return item.paidAmount <= 0 && item.remainingAmount > 0;
  }
  return true;
}

async function buildCustomerAccounts(status = "all") {
  const orderFinance = (await getDeliveryFinanceEntries()).filter((item) => item.status === "done");
  const grouped = new Map();

  for (const order of orderFinance) {
    const key = safeString(order.customerName, 120) || "Nomsiz zakazchi";
    if (!grouped.has(key)) {
      grouped.set(key, {
        customerName: key,
        totalOrders: 0,
        totalAmount: 0,
        paidAmount: 0,
        remainingAmount: 0,
        lastOrderDate: order.date,
        orders: [],
      });
    }

    const current = grouped.get(key);
    current.totalOrders += 1;
    current.totalAmount = roundMoney(current.totalAmount + order.revenue);
    current.paidAmount = roundMoney(current.paidAmount + order.paidAmount);
    current.remainingAmount = roundMoney(current.remainingAmount + order.remainingAmount);
    current.lastOrderDate = String(order.date) > String(current.lastOrderDate) ? order.date : current.lastOrderDate;
    current.orders.push(order);
  }

  const accounts = [...grouped.values()]
    .map((item) => ({
      ...item,
      paymentStatus: paymentStatusFromAmounts(item.totalAmount, item.paidAmount),
      orders: item.orders
        .sort((left, right) => String(right.date).localeCompare(String(left.date)))
        .slice(0, 6),
    }))
    .filter((item) => filterCustomerAccountByStatus(item, status))
    .sort((left, right) => {
      if (right.remainingAmount !== left.remainingAmount) {
        return right.remainingAmount - left.remainingAmount;
      }
      return String(right.lastOrderDate).localeCompare(String(left.lastOrderDate));
    });

  const recentPayments = await collections.customerPayments.find({}).sort({ date: -1, createdAt: -1 }).limit(20).toArray();
  const paymentTaskMap = new Map();
  const taskIds = [...new Set(recentPayments.map((item) => normalizeIdString(item.taskId)).filter(Boolean))]
    .filter((id) => ObjectId.isValid(id))
    .map((id) => new ObjectId(id));
  const tasks = taskIds.length ? await collections.tasks.find({ _id: { $in: taskIds } }).toArray() : [];
  for (const task of tasks) {
    paymentTaskMap.set(normalizeIdString(task._id), task);
  }

  return {
    accounts,
    recentPayments: recentPayments.map((payment) => ({
      id: normalizeIdString(payment._id),
      amount: roundMoney(payment.amount || 0),
      date: safeString(payment.date, 10),
      note: payment.note || "",
      customerName: payment.customerName || paymentTaskMap.get(normalizeIdString(payment.taskId))?.customerName || "",
      taskId: normalizeIdString(payment.taskId) || "",
    })),
  };
}

function buildStaffSalaryEntries(users = [], maxMonthKey = toMonthKey()) {
  const startMonthKey = `${maxMonthKey.slice(0, 4)}-01`;
  const monthKeys = listMonthKeysBetween(startMonthKey, maxMonthKey);
  const entries = [];

  for (const user of users) {
    const amount = roundMoney(user.salaryAmount || 0);
    if (amount <= 0 || user.role === "worker") {
      continue;
    }

    const createdMonthKey = toMonthKey(user.createdAt || new Date());
    for (const monthKey of monthKeys) {
      if (compareMonthKeys(monthKey, createdMonthKey) < 0) {
        continue;
      }
      entries.push({
        userId: normalizeIdString(user._id),
        date: buildMonthDate(monthKey, clampNumber(user.salaryDayOfMonth || 5, 1, 31, 5)),
        amount,
      });
    }
  }

  return entries;
}

async function getUserMapByIds(ids = []) {
  const uniqueIds = [...new Set(ids.map((item) => normalizeIdString(item)).filter(Boolean))];
  const objectIds = uniqueIds.filter((id) => ObjectId.isValid(id)).map((id) => new ObjectId(id));
  const users = objectIds.length ? await collections.users.find({ _id: { $in: objectIds } }).toArray() : [];
  return new Map(users.map((user) => [normalizeIdString(user._id), serializeUser(user)]));
}

async function createNotification({ userId, title, body, type = "info", link = "", meta = {} }) {
  if (!userId) {
    return null;
  }

  const now = new Date();
  const document = {
    userId: toStoredId(userId) || normalizeIdString(userId),
    type: safeString(type, 40) || "info",
    title: safeString(title, 120),
    body: safeString(body, 600),
    link: safeString(link, 200),
    meta: isPlainObject(meta) ? cloneValue(meta) : {},
    createdAt: now,
    updatedAt: now,
    readAt: null,
  };

  const result = await collections.notifications.insertOne(document);
  return { ...document, _id: result.insertedId };
}

async function createNotificationBatch(userIds = [], payload = {}) {
  const uniqueIds = [...new Set(userIds.map((item) => normalizeIdString(item)).filter(Boolean))];
  const created = [];
  for (const userId of uniqueIds) {
    created.push(await createNotification({ ...payload, userId }));
  }
  return created;
}

function getCurrentPeriodRanges() {
  const today = getYmd();
  const weekStart = shiftYmd(today, 1 - getWeekdayFromYmd(today));
  return {
    daily: { label: "Kunlik", start: today, end: today },
    weekly: { label: "Haftalik", start: weekStart, end: today },
    monthly: { label: "Oylik", start: `${today.slice(0, 7)}-01`, end: today },
    yearly: { label: "Yillik", start: `${today.slice(0, 4)}-01-01`, end: today },
  };
}

function getTaskAccountingDate(task) {
  if (task.completedAt) {
    return getYmd(new Date(task.completedAt));
  }
  if (task.updatedAt) {
    return getYmd(new Date(task.updatedAt));
  }
  return task.scheduledDate;
}

function buildOrderFinance(task, financeSettings) {
  const payment = buildTaskPaymentSnapshot(task, task.paidAmount || 0, financeSettings);
  const quantity = Math.max(0, Math.round(parseNumber(task.quantity, 0)));
  const nonLaborExpense = roundMoney(quantity * financeSettings.nonLaborCostPerBrick);
  const pieceworkExpense = roundMoney(quantity * financeSettings.laborCostPerBrick);
  const totalExpense = roundMoney(nonLaborExpense + pieceworkExpense);
  const profit = roundMoney(payment.orderTotal - totalExpense);
  return {
    taskId: normalizeIdString(task._id),
    customerName: task.customerName,
    quantity,
    date: getTaskAccountingDate(task),
    revenue: payment.orderTotal,
    paidAmount: payment.paidAmount,
    remainingAmount: payment.remainingAmount,
    paymentStatus: payment.paymentStatus,
    nonLaborExpense,
    pieceworkExpense,
    brickExpense: totalExpense,
    profit,
  };
}

async function ensureYearPayrollRecords() {
  return null;
}

async function ensureSalaryDueNotifications() {
  const today = getYmd();
  const currentMonthKey = toMonthKey(today);
  const users = await collections.users.find({ isActive: true }).toArray();
  const payrolls = await buildPayrollSnapshots({ monthKey: currentMonthKey, users });

  for (const record of payrolls) {
    const userId = record.user?.id;
    if (!userId) {
      continue;
    }

    if (record.payableAmount > 0 && String(record.dueDate) <= today) {
      const existing = await collections.notifications.findOne({
        userId: toStoredId(userId) || userId,
        type: "salary_due",
        monthKey: currentMonthKey,
      });

      if (!existing) {
        await collections.notifications.insertOne({
          userId: toStoredId(userId) || userId,
          type: "salary_due",
          monthKey: currentMonthKey,
          title: "Hisob-kitob muddati yetdi",
          body: `${currentMonthKey} uchun ${record.payableAmount} so'm to'lov kutilmoqda.`,
          link: "/profile.html",
          meta: { monthKey: currentMonthKey, payableAmount: record.payableAmount },
          createdAt: new Date(),
          updatedAt: new Date(),
          readAt: null,
        });
      }
    }

    if (record.debtAmount <= 0) {
      continue;
    }

    const existing = await collections.notifications.findOne({
      userId: toStoredId(userId) || userId,
      type: "worker_debt",
      monthKey: currentMonthKey,
    });

    if (existing) {
      continue;
    }

    await collections.notifications.insertOne({
      userId: toStoredId(userId) || userId,
      type: "worker_debt",
      monthKey: currentMonthKey,
      title: "Qarz balansi mavjud",
      body: `${currentMonthKey} bo'yicha ${record.debtAmount} so'm qarz balansi ko'rinmoqda.`,
      link: "/profile.html",
      meta: { monthKey: currentMonthKey, debtAmount: record.debtAmount },
      createdAt: new Date(),
      updatedAt: new Date(),
      readAt: null,
    });
  }
}

async function ensureBusinessState() {
  await ensureSalaryDueNotifications();
}

async function buildFinanceDashboard() {
  await ensureBusinessState();

  const financeSettings = await getFinanceSettings();
  const todayMonthKey = toMonthKey();
  const [orderFinanceAll, customerPayments, workLogs, users, payroll, customerAccounts, recentTransactionsRaw] = await Promise.all([
    getDeliveryFinanceEntries(financeSettings),
    collections.customerPayments.find({}).toArray(),
    collections.workLogs.find({}).sort({ date: -1, createdAt: -1 }).toArray(),
    collections.users.find({ isActive: true }).toArray(),
    buildPayrollSnapshots({ monthKey: todayMonthKey }),
    buildCustomerAccounts("all"),
    collections.workerTransactions.find({}).sort({ date: -1, createdAt: -1 }).limit(20).toArray(),
  ]);
  const periods = getCurrentPeriodRanges();
  const orderFinance = orderFinanceAll.filter((item) => item.status === "done");
  const pieceworkEntries = workLogs.map((item) => ({
    date: safeString(item.date, 10),
    amount: roundMoney(item.totalAmount || 0),
  }));
  const staffPayrollEntries = buildStaffSalaryEntries(users, todayMonthKey);

  const periodSummary = Object.fromEntries(
    Object.entries(periods).map(([key, period]) => {
      const orders = orderFinance.filter((item) => isYmdWithinRange(item.date, period.start, period.end));
      const payments = customerPayments.filter((item) => isYmdWithinRange(item.date, period.start, period.end));
      const pieceworkExpense = roundMoney(pieceworkEntries
        .filter((item) => isYmdWithinRange(item.date, period.start, period.end))
        .reduce((sum, item) => sum + item.amount, 0));
      const payrollExpense = roundMoney(staffPayrollEntries
        .filter((item) => isYmdWithinRange(item.date, period.start, period.end))
        .reduce((sum, item) => sum + item.amount, 0));
      const revenue = roundMoney(orders.reduce((sum, item) => sum + item.revenue, 0));
      const collectedCash = roundMoney(payments.reduce((sum, item) => sum + roundMoney(item.amount || 0), 0));
      const nonLaborExpense = roundMoney(orders.reduce((sum, item) => sum + item.nonLaborExpense, 0));
      const receivableAmount = roundMoney(orders.reduce((sum, item) => sum + item.remainingAmount, 0));
      const totalExpense = roundMoney(nonLaborExpense + pieceworkExpense + payrollExpense);
      return [key, {
        ...period,
        ordersCount: orders.length,
        bricksCount: orders.reduce((sum, item) => sum + item.quantity, 0),
        revenue,
        collectedCash,
        receivableAmount,
        nonLaborExpense,
        pieceworkExpense,
        brickExpense: roundMoney(nonLaborExpense + pieceworkExpense),
        payrollExpense,
        totalExpense,
        grossProfit: roundMoney(revenue - nonLaborExpense - pieceworkExpense),
        netProfit: roundMoney(revenue - totalExpense),
      }];
    }),
  );

  return {
    settings: financeSettings,
    periods: periodSummary,
    recentOrders: orderFinance
      .sort((left, right) => String(right.date).localeCompare(String(left.date)))
      .slice(0, 12),
    payroll: payroll
      .sort((left, right) => {
        if (right.debtAmount !== left.debtAmount) {
          return right.debtAmount - left.debtAmount;
        }
        return right.payableAmount - left.payableAmount;
      })
      .slice(0, 20),
    workerBalances: payroll
      .filter((item) => item.debtAmount > 0 || item.payableAmount > 0 || item.workLogCount > 0)
      .sort((left, right) => {
        const rightExposure = Math.max(right.debtAmount, right.payableAmount);
        const leftExposure = Math.max(left.debtAmount, left.payableAmount);
        return rightExposure - leftExposure;
      })
      .slice(0, 20),
    customerAccounts: customerAccounts.accounts.slice(0, 12),
    recentPayments: customerAccounts.recentPayments.slice(0, 12),
    recentWorkLogs: await enrichWorkLogs(workLogs.slice(0, 12)),
    recentTransactions: await enrichWorkerTransactions(recentTransactionsRaw),
  };
}

function dedupeValue(baseValue, usedValues, fallbackValue) {
  let candidate = safeString(baseValue, 80) || fallbackValue;
  let counter = 1;

  while (usedValues.has(candidate)) {
    counter += 1;
    candidate = `${fallbackValue}-${counter}`;
  }

  usedValues.add(candidate);
  return candidate;
}

async function migrateLegacyUsers() {
  const users = await collections.users.find({}).sort({ createdAt: 1 }).toArray();
  const usedUsernames = new Set();
  let fixedCount = 0;

  for (const user of users) {
    const idSuffix = user._id.toString().slice(-6).toLowerCase();
    const rawUsername = safeString(user.username, 40);
    const preferredUsername = rawUsername || `user-${idSuffix}`;
    const preferredLower = normalizeUsername(user.usernameLower || preferredUsername)
      .replace(/\s+/g, "-")
      .replace(/[^a-z0-9._-]/g, "") || `user-${idSuffix}`;

    const finalLower = dedupeValue(preferredLower, usedUsernames, `user-${idSuffix}`);
    const finalUsername = rawUsername && normalizeUsername(rawUsername) === finalLower
      ? rawUsername
      : finalLower;

    const needsUpdate =
      user.username !== finalUsername ||
      user.usernameLower !== finalLower ||
      typeof user.isActive !== "boolean";

    if (needsUpdate) {
      await collections.users.updateOne(
        { _id: user._id },
        {
          $set: {
            username: finalUsername,
            usernameLower: finalLower,
            isActive: typeof user.isActive === "boolean" ? user.isActive : true,
            updatedAt: new Date(),
          },
        },
      );
      fixedCount += 1;
    }
  }

  if (fixedCount > 0) {
    console.warn(`Mongo migration: ${fixedCount} ta user yozuvi tiklandi.`);
  }
}

async function migrateLegacyContents() {
  const items = await collections.contents.find({}).sort({ createdAt: 1 }).toArray();
  const usedSlugs = new Set();
  let fixedCount = 0;

  for (const item of items) {
    const idSuffix = item._id.toString().slice(-6).toLowerCase();
    const baseSlug = slugify(item.slug || item.title || `${item.type || "content"}-${idSuffix}`) || `content-${idSuffix}`;
    const finalSlug = dedupeValue(baseSlug, usedSlugs, `content-${idSuffix}`);
    const needsUpdate = item.slug !== finalSlug;

    if (needsUpdate) {
      await collections.contents.updateOne(
        { _id: item._id },
        {
          $set: {
            slug: finalSlug,
            updatedAt: new Date(),
          },
        },
      );
      fixedCount += 1;
    }
  }

  if (fixedCount > 0) {
    console.warn(`Mongo migration: ${fixedCount} ta content slug tiklandi.`);
  }
}

async function migrateMongoDocuments() {
  if (storageMode !== "mongo") {
    return;
  }

  await migrateLegacyUsers();
  await migrateLegacyContents();
}

async function ensureCollectionIndex(collection, key, options = {}) {
  if (storageMode !== "mongo") {
    return collection.createIndex(key, options);
  }

  const name = options.name || Object.entries(key).map(([field, direction]) => `${field}_${direction}`).join("_");

  try {
    return await collection.createIndex(key, { ...options, name });
  } catch (error) {
    const isConflict =
      error?.codeName === "IndexOptionsConflict" ||
      error?.codeName === "IndexKeySpecsConflict" ||
      /already exists with different options/i.test(error?.message || "");

    if (!isConflict) {
      throw error;
    }

    await collection.dropIndex(name).catch(() => null);
    return collection.createIndex(key, { ...options, name });
  }
}

async function ensureIndexes() {
  await Promise.all([
    ensureCollectionIndex(collections.users, { usernameLower: 1 }, {
      unique: true,
      partialFilterExpression: { usernameLower: { $type: "string" } },
    }),
    ensureCollectionIndex(collections.sessions, { tokenHash: 1 }, { unique: true }),
    ensureCollectionIndex(collections.sessions, { expiresAt: 1 }, { expireAfterSeconds: 0 }),
    ensureCollectionIndex(collections.contents, { type: 1, isPublished: 1, createdAt: -1 }),
    ensureCollectionIndex(collections.contents, { slug: 1 }, {
      unique: true,
      partialFilterExpression: { slug: { $type: "string" } },
    }),
    ensureCollectionIndex(collections.tasks, { scheduledDate: 1, type: 1, status: 1 }),
    ensureCollectionIndex(collections.settings, { key: 1 }, {
      unique: true,
      partialFilterExpression: { key: { $type: "string" } },
    }),
    ensureCollectionIndex(collections.notifications, { userId: 1, createdAt: -1 }),
    ensureCollectionIndex(collections.payrolls, { userId: 1, monthKey: 1 }, {
      unique: true,
      partialFilterExpression: { monthKey: { $type: "string" } },
    }),
    ensureCollectionIndex(collections.workLogs, { date: -1, workType: 1 }),
    ensureCollectionIndex(collections.workerTransactions, { workerId: 1, date: -1 }),
    ensureCollectionIndex(collections.customerPayments, { taskId: 1, date: -1 }),
    ensureCollectionIndex(collections.cameraCounts, { monitorId: 1, date: -1 }, {
      unique: true,
      partialFilterExpression: { monitorId: { $type: "string" }, date: { $type: "string" } },
    }),
  ]);
}

async function createUserIfMissing({ fullName, username, password, role }) {
  const usernameLower = normalizeUsername(username);
  const existing = await collections.users.findOne({ usernameLower });
  if (existing) {
    return existing;
  }

  const normalizedRole = normalizeRole(role, "worker");
  const passwordHash = await hashPassword(password);
  const now = new Date();
  const document = {
    fullName: safeString(fullName, 80),
    username: safeString(username, 40),
    usernameLower,
    passwordHash,
    role: normalizedRole,
    positionTitle: defaultPositionTitleForRole(normalizedRole),
    phone: "",
    bio: "",
    avatarUrl: "",
    salaryAmount: 0,
    salaryDayOfMonth: 5,
    assignedWorkType: normalizedRole === "worker" ? "parmofka" : "",
    isActive: true,
    createdAt: now,
    updatedAt: now,
  };

  const result = await collections.users.insertOne(document);
  console.log(`[seed] ${role} foydalanuvchi yaratildi: ${username} / ${password}`);
  return { ...document, _id: result.insertedId };
}

async function seedUsers() {
  const createdUsers = {};

  createdUsers.admin = await createUserIfMissing({
    fullName: "Bosh Admin",
    username: process.env.SEED_ADMIN_USERNAME || "admin",
    password: process.env.SEED_ADMIN_PASSWORD || "Admin123!",
    role: "admin",
  });

  if (process.env.AUTO_SEED_DEMO_USERS !== "false") {
    createdUsers.organizer = await createUserIfMissing({
      fullName: "Bosh Organizer",
      username: process.env.SEED_ORGANIZER_USERNAME || "organizer",
      password: process.env.SEED_ORGANIZER_PASSWORD || "Organizer123!",
      role: "organizer",
    });

    createdUsers.worker = await createUserIfMissing({
      fullName: "Namuna Ishchi",
      username: process.env.SEED_WORKER_USERNAME || "worker",
      password: process.env.SEED_WORKER_PASSWORD || "Worker123!",
      role: "worker",
    });
  }

  return createdUsers;
}

async function ensureDefaultSettings(seedActors = {}) {
  const existingFinance = await collections.settings.findOne({ key: "finance" });
  if (!existingFinance) {
    await setSettingValue("finance", normalizeFinanceSettings({}), seedActors.admin?._id || null);
  }
}

async function seedContent() {
  const count = await collections.contents.countDocuments({});
  if (count > 0) {
    return;
  }

  const now = new Date();
  const templates = [
    {
      type: "product",
      title: "Premium Qurilish G'ishti",
      excerpt: "Yuqori bosimga chidamli, fasad va asosiy qurilish ishlari uchun mos partiya.",
      body: "Mazkur mahsulot zich pishirilgan xomashyodan tayyorlanadi. Bir xil o'lcham, silliq kesim va yuqori mustahkamlik bilan doimiy partiya nazoratidan o'tadi.",
      priceLabel: "So'rov bo'yicha",
      tags: ["Premium", "Fasad", "Mustahkam"],
    },
    {
      type: "product",
      title: "Standart Qizil G'isht",
      excerpt: "Kundalik obyektlar uchun balansli narx va sifat yechimi.",
      body: "Standart liniyada ishlab chiqarilgan ushbu tur yirik va o'rta hajmdagi qurilish buyurtmalari uchun barqaror yetkazib berish grafigi bilan taqdim etiladi.",
      priceLabel: "Ulguji narx mavjud",
      tags: ["Standart", "Ulguji", "Barqaror"],
    },
    {
      type: "news",
      title: "Yangi Partiya Nazorat Moduli Ishga Tushdi",
      excerpt: "Zavod ichki nazoratida har bir topshiriq status bo'yicha kuzatiladi.",
      body: "Yangi platforma yordamida ertalik reja, ishlab chiqarish jarayoni va topshirish holati endi rollar kesimida ko'rinadi. Bu sifat va tezlikni oshiradi.",
      tags: ["Platforma", "Nazorat", "Yangilik"],
    },
    {
      type: "news",
      title: "Yetkazib Berish Oqimi Raqamlashtirildi",
      excerpt: "Topshirilgan g'ishtlar endi buyurtmachi bo'yicha alohida qayd etiladi.",
      body: "Har bir zakazchi uchun topshirish soni alohida kartalarda yuritiladi. Organizer va admin panelda kunlik kesim ko'rsatkichlari yangilanadi.",
      tags: ["Yetkazib berish", "Hisobot", "Zakazchi"],
    },
    {
      type: "blog",
      title: "Ertalik Rejani To'g'ri Tuzish Bo'yicha 5 Qoida",
      excerpt: "Quyish va topshirish oqimini bir sahifada boshqarish uchun amaliy tavsiyalar.",
      body: "Ertalik reja tuzilganda buyurtmachi nomi, miqdor, tur va muddat aniq kiritilishi kerak. Ishchi topshiriqni qabul qilgach, jarayonni status bilan yangilashi nazoratni yengillashtiradi.",
      tags: ["Reja", "Organizer", "Amaliyot"],
    },
    {
      type: "blog",
      title: "Ishchi Paneldagi Statuslar Nega Muhim",
      excerpt: "Planned, accepted, in progress va done bosqichlari ma'lumot yo'qolishini kamaytiradi.",
      body: "Statuslar oddiy ko'rinsa ham, ular ishlab chiqarishdagi real yuklama va topshirilmagan buyurtmalarni bir qarashda ko'rishga yordam beradi.",
      tags: ["Status", "Ishchi", "Nazorat"],
    },
  ];

  const documents = templates.map((item) => ({
    type: item.type,
    title: item.title,
    slug: `${slugify(item.title)}-${crypto.randomBytes(3).toString("hex")}`,
    excerpt: item.excerpt,
    body: item.body,
    imageUrl: makePlaceholderDataUrl(
      item.title,
      item.type === "product" ? "#fdba74" : item.type === "news" ? "#fda4af" : "#93c5fd",
      item.type === "product" ? "#9a3412" : item.type === "news" ? "#9f1239" : "#1d4ed8",
    ),
    priceLabel: item.priceLabel || "",
    tags: item.tags || [],
    isPublished: true,
    createdAt: now,
    updatedAt: now,
  }));

  await collections.contents.insertMany(documents);
}

async function seedTasks(seedActors) {
  const count = await collections.tasks.countDocuments({});
  if (count > 0) {
    return;
  }

  const organizer = seedActors.organizer || seedActors.admin;
  const worker = seedActors.worker || seedActors.admin;
  const now = new Date();
  const today = getYmd();
  const tomorrow = getTomorrowYmd();
  const tasks = [
    {
      type: "production",
      customerName: "Samandar Qurilish",
      quantity: 1000,
      scheduledDate: tomorrow,
      status: "planned",
      notes: "Ertalik quyish partiyasi",
      createdBy: organizer._id,
      progressNotes: [],
      createdAt: now,
      updatedAt: now,
    },
    {
      type: "production",
      customerName: "Nur Invest",
      quantity: 350,
      scheduledDate: tomorrow,
      status: "planned",
      notes: "Tez tayyorlanadigan partiya",
      createdBy: organizer._id,
      progressNotes: [],
      createdAt: now,
      updatedAt: now,
    },
    {
      type: "delivery",
      customerName: "Obod Uylar",
      quantity: 1500,
      scheduledDate: today,
      status: "in_progress",
      notes: "Oldin quyilgan va tayyor partiya",
      createdBy: organizer._id,
      acceptedBy: worker._id,
      acceptedAt: now,
      progressNotes: [
        { note: "Topshiriq qabul qilindi", status: "accepted", at: now, byRole: worker.role },
      ],
      createdAt: now,
      updatedAt: now,
    },
    {
      type: "delivery",
      customerName: "Mega Stroy",
      quantity: 780,
      scheduledDate: today,
      status: "done",
      notes: "Tayyor mahsulot topshirildi",
      createdBy: organizer._id,
      acceptedBy: worker._id,
      completedBy: worker._id,
      acceptedAt: now,
      completedAt: now,
      progressNotes: [
        { note: "Topshiriq qabul qilindi", status: "accepted", at: now, byRole: worker.role },
        { note: "Topshiriq bajarildi", status: "done", at: now, byRole: worker.role },
      ],
      createdAt: now,
      updatedAt: now,
    },
  ];

  await collections.tasks.insertMany(tasks);
}

async function connectDatabase() {
  const useLocalStorage = async (reason) => {
    storageMode = "local";
    ObjectId = LocalObjectId;
    collections = await createLocalCollections();
    if (reason) {
      console.warn(`MongoDB ulanmagan: ${reason}`);
    }
    console.warn(`Server local storage rejimiga o'tdi: ${LOCAL_DB_FILE}`);
  };

  let initialized = false;

  if (!MongoClient) {
    await useLocalStorage("mongodb drayveri topilmadi");
  } else {
    try {
      mongoClient = new MongoClient(MONGODB_URI, {
        serverSelectionTimeoutMS: MONGO_CONNECT_TIMEOUT_MS,
      });
      await mongoClient.connect();

      const database = mongoClient.db(DB_NAME);
      collections = {
        users: database.collection("users"),
        sessions: database.collection("sessions"),
        tasks: database.collection("tasks"),
        contents: database.collection("contents"),
        settings: database.collection("settings"),
        notifications: database.collection("notifications"),
        payrolls: database.collection("payrolls"),
        workLogs: database.collection("workLogs"),
        workerTransactions: database.collection("workerTransactions"),
        customerPayments: database.collection("customerPayments"),
        cameraCounts: database.collection("cameraCounts"),
      };
      storageMode = "mongo";
      await migrateMongoDocuments();
      await ensureIndexes();
      const seededUsers = await seedUsers();
      await ensureDefaultSettings(seededUsers);
      await seedContent();
      await seedTasks(seededUsers);
      initialized = true;
    } catch (error) {
      await mongoClient?.close().catch(() => null);
      mongoClient = null;
      await useLocalStorage(`Mongo init xatosi: ${error.message}`);
    }
  }

  if (!initialized) {
    await ensureIndexes();
    const seededUsers = await seedUsers();
    await ensureDefaultSettings(seededUsers);
    await seedContent();
    await seedTasks(seededUsers);
  }
}

async function handleLogin(request, response) {
  const body = await readBody(request);
  const usernameLower = normalizeUsername(body.username);
  const password = String(body.password || "");

  if (!usernameLower || !password) {
    return sendJson(response, 400, { error: "Login va parol majburiy." });
  }

  const user = await collections.users.findOne({ usernameLower });

  if (!user || !user.isActive) {
    return sendJson(response, 401, { error: "Login yoki parol noto'g'ri." });
  }

  const passwordValid = await verifyPassword(password, user.passwordHash);

  if (!passwordValid) {
    return sendJson(response, 401, { error: "Login yoki parol noto'g'ri." });
  }

  const session = await createSession(user);
  await collections.users.updateOne(
    { _id: user._id },
    { $set: { lastLoginAt: new Date(), updatedAt: new Date() } },
  );

  sendJson(
    response,
    200,
    {
      ok: true,
      user: serializeUser(user),
      redirectTo: mapDashboardPath(user.role),
    },
    { "Set-Cookie": buildSessionCookie(session.token) },
  );
}

async function handleLogout(request, response) {
  const cookies = parseCookies(request.headers.cookie || "");
  const token = cookies[SESSION_COOKIE];
  if (token) {
    await collections.sessions.deleteOne({ tokenHash: sha256(token) });
  }
  sendJson(response, 200, { ok: true }, { "Set-Cookie": buildClearCookie() });
}

async function handleAuthMe(request, response) {
  const context = await getSessionContext(request);
  if (!context || context.invalid) {
    return sendJson(
      response,
      200,
      { authenticated: false },
      context?.invalid ? { "Set-Cookie": buildClearCookie() } : {},
    );
  }
  return sendJson(response, 200, {
    authenticated: true,
    user: context.safeUser,
    redirectTo: mapDashboardPath(context.user.role),
  });
}

async function handleUsersList(request, response) {
  const auth = await requireAuth(request, response, ["admin"]);
  if (!auth) {
    return;
  }

  const users = await collections.users.find({}).sort({ createdAt: -1 }).toArray();
  sendJson(response, 200, { users: users.map(serializeUser) });
}

async function handleUserCreate(request, response) {
  const auth = await requireAuth(request, response, ["admin"]);
  if (!auth) {
    return;
  }

  const body = await readBody(request);
  const fullName = safeString(body.fullName, 80);
  const username = safeString(body.username, 40);
  const usernameLower = normalizeUsername(username);
  const password = String(body.password || "");
  const role = normalizeRole(body.role, "");
  const positionTitle = normalizePositionTitle(role, body.positionTitle);
  const phone = safeString(body.phone, 40);
  const bio = safeString(body.bio, 500);
  const avatarUrl = safeString(body.avatarUrl, 4000);
  const assignedWorkType = normalizeWorkType(body.assignedWorkType, "");

  if (!role) {
    return sendJson(response, 400, { error: "Rol noto'g'ri." });
  }

  if (!fullName || !usernameLower || password.length < 6) {
    return sendJson(response, 400, { error: "Ism, login va kamida 6 belgili parol kiriting." });
  }

  if (role === "worker" && !assignedWorkType) {
    return sendJson(response, 400, { error: "Ishchi uchun bitta ishlov turi tanlanishi shart." });
  }

  const salaryAmount = role === "worker"
    ? 0
    : Math.max(0, roundMoney(body.salaryAmount || 0));
  const salaryDayOfMonth = role === "worker"
    ? 5
    : clampNumber(body.salaryDayOfMonth || 5, 1, 31, 5);

  const existing = await collections.users.findOne({ usernameLower });
  if (existing) {
    return sendJson(response, 409, { error: "Bu login band." });
  }

  const now = new Date();
  const user = {
    fullName,
    username,
    usernameLower,
    passwordHash: await hashPassword(password),
    role,
    positionTitle,
    phone,
    bio,
    avatarUrl,
    salaryAmount,
    salaryDayOfMonth,
    assignedWorkType: role === "worker" ? assignedWorkType : "",
    isActive: true,
    createdAt: now,
    updatedAt: now,
  };

  const result = await collections.users.insertOne(user);
  await reloadCameraMonitorService().catch(() => null);
  sendJson(response, 201, { ok: true, user: serializeUser({ ...user, _id: result.insertedId }) });
}

async function handleUserUpdate(request, response, id) {
  const auth = await requireAuth(request, response, ["admin"]);
  if (!auth) {
    return;
  }

  if (!ObjectId.isValid(id)) {
    return sendJson(response, 400, { error: "User ID noto'g'ri." });
  }

  const body = await readBody(request);
  const update = {
    updatedAt: new Date(),
  };
  const currentUser = await collections.users.findOne({ _id: new ObjectId(id) });

  if (!currentUser) {
    return sendJson(response, 404, { error: "Foydalanuvchi topilmadi." });
  }

  const nextRole = typeof body.role === "string"
    ? normalizeRole(body.role, currentUser.role)
    : normalizeRole(currentUser.role, "worker");

  if (typeof body.fullName === "string") {
    update.fullName = safeString(body.fullName, 80);
  }
  if (typeof body.username === "string") {
    const username = safeString(body.username, 40);
    const usernameLower = normalizeUsername(username);

    if (!usernameLower) {
      return sendJson(response, 400, { error: "Login noto'g'ri." });
    }

    if (usernameLower !== currentUser.usernameLower) {
      const existing = await collections.users.findOne({ usernameLower });
      if (normalizeIdString(existing?._id) !== normalizeIdString(currentUser?._id)) {
        return sendJson(response, 409, { error: "Bu login band." });
      }
    }

    update.username = username;
    update.usernameLower = usernameLower;
  }
  if (typeof body.role === "string") {
    update.role = nextRole;
  }
  if (typeof body.positionTitle === "string") {
    update.positionTitle = normalizePositionTitle(nextRole, body.positionTitle);
  } else if (typeof body.role === "string") {
    update.positionTitle = normalizePositionTitle(nextRole, currentUser.positionTitle);
  }
  if (typeof body.phone === "string") {
    update.phone = safeString(body.phone, 40);
  }
  if (typeof body.bio === "string") {
    update.bio = safeString(body.bio, 500);
  }
  if (typeof body.avatarUrl === "string") {
    update.avatarUrl = safeString(body.avatarUrl, 4000);
  }
  if (typeof body.salaryAmount !== "undefined" && nextRole !== "worker") {
    update.salaryAmount = Math.max(0, roundMoney(body.salaryAmount || 0));
  }
  if (typeof body.salaryDayOfMonth !== "undefined" && nextRole !== "worker") {
    update.salaryDayOfMonth = clampNumber(body.salaryDayOfMonth || 5, 1, 31, 5);
  }
  if (nextRole === "worker") {
    update.salaryAmount = 0;
    update.salaryDayOfMonth = 5;
  }
  if (typeof body.assignedWorkType !== "undefined" || typeof body.role !== "undefined") {
    const nextAssignedWorkType = normalizeWorkType(
      typeof body.assignedWorkType !== "undefined" ? body.assignedWorkType : currentUser.assignedWorkType,
      "",
    );
    if (nextRole === "worker" && !nextAssignedWorkType) {
      return sendJson(response, 400, { error: "Ishchi uchun bitta ishlov turi biriktirilishi kerak." });
    }
    update.assignedWorkType = nextRole === "worker" ? nextAssignedWorkType : "";
  }
  if (typeof body.isActive !== "undefined") {
    update.isActive = parseBoolean(body.isActive, true);
  }
  if (typeof body.password === "string" && body.password.trim().length >= 6) {
    update.passwordHash = await hashPassword(body.password.trim());
  }

  const userId = new ObjectId(id);
  await collections.users.updateOne({ _id: userId }, { $set: update });

  if (body.isActive === false || body.isActive === "false") {
    await collections.sessions.deleteMany({ userId });
  }

  const updatedUser = await collections.users.findOne({ _id: userId });
  await reloadCameraMonitorService().catch(() => null);
  sendJson(response, 200, { ok: true, user: serializeUser(updatedUser) });
}

async function handleUserDelete(request, response, id) {
  const auth = await requireAuth(request, response, ["admin"]);
  if (!auth) {
    return;
  }

  if (!ObjectId.isValid(id)) {
    return sendJson(response, 400, { error: "User ID noto'g'ri." });
  }

  const userId = new ObjectId(id);
  const targetUser = await collections.users.findOne({ _id: userId });
  if (!targetUser) {
    return sendJson(response, 404, { error: "Foydalanuvchi topilmadi." });
  }

  if (normalizeIdString(targetUser._id) === normalizeIdString(auth.user._id)) {
    return sendJson(response, 400, { error: "O'zingizni o'chira olmaysiz." });
  }

  if (targetUser.role === "admin") {
    const admins = await collections.users.find({ role: "admin", isActive: true }).toArray();
    if (admins.length <= 1) {
      return sendJson(response, 400, { error: "Oxirgi admin foydalanuvchini o'chirib bo'lmaydi." });
    }
  }

  if (targetUser.role === "worker") {
    const [workLogCount, transactionCount] = await Promise.all([
      collections.workLogs.countDocuments({ workerIds: userId }),
      collections.workerTransactions.countDocuments({ workerId: userId }),
    ]);

    if (workLogCount > 0 || transactionCount > 0) {
      return sendJson(response, 400, {
        error: "Bu ishchida hisob-kitob tarixi bor. O'chirish o'rniga nofaol holatga o'tkazing.",
      });
    }
  }

  await collections.users.deleteOne({ _id: userId });
  await collections.sessions.deleteMany({ userId });
  await collections.notifications.deleteMany({ userId });
  await collections.payrolls.deleteMany({ userId });
  await reloadCameraMonitorService().catch(() => null);
  sendJson(response, 200, { ok: true });
}

function validateTaskInput(body) {
  const type = safeString(body.type, 20);
  const workType = normalizeWorkType(body.workType, "");
  const customerName = safeString(body.customerName, 120);
  const quantity = Number(body.quantity);
  const scheduledDate = safeString(body.scheduledDate, 20);
  const notes = safeString(body.notes, 500);

  if (!["production", "delivery"].includes(type)) {
    return { error: "Topshiriq turi noto'g'ri." };
  }

  if (!customerName || !Number.isFinite(quantity) || quantity <= 0 || !scheduledDate) {
    return { error: "Zakazchi, son va sana majburiy." };
  }

  return {
    value: {
      type,
      workType,
      customerName,
      quantity: Math.round(quantity),
      scheduledDate,
      notes,
    },
  };
}

async function validateWorkLogInput(body) {
  const date = safeString(body.date, 10) || getYmd();
  const workType = normalizeWorkType(body.workType, "");
  const quantity = Math.round(Number(body.quantity));
  const notes = safeString(body.notes, 500);
  const workerIds = Array.isArray(body.workerIds)
    ? body.workerIds
    : typeof body.workerIds === "string"
      ? body.workerIds.split(",")
      : [];
  const uniqueWorkerIds = [...new Set(workerIds.map((item) => safeString(item, 40)).filter(Boolean))];

  if (!workType) {
    return { error: "Ishlov turi noto'g'ri." };
  }

  if (!date || !Number.isFinite(quantity) || quantity <= 0) {
    return { error: "Sana va miqdor majburiy." };
  }

  if (uniqueWorkerIds.length < 1 || uniqueWorkerIds.length > 10) {
    return { error: "Bir yozuvga 1 tadan 10 tagacha ishchi biriktiriladi." };
  }

  if (uniqueWorkerIds.some((item) => !ObjectId.isValid(item))) {
    return { error: "Ishchi ro'yxatida xato bor." };
  }

  const workers = await collections.users.find({
    _id: { $in: uniqueWorkerIds.map((item) => new ObjectId(item)) },
    role: "worker",
    isActive: true,
  }).toArray();

  if (workers.length !== uniqueWorkerIds.length) {
    return { error: "Tanlangan ishchilardan biri topilmadi yoki faol emas." };
  }

  const mismatch = workers.find((item) => normalizeWorkType(item.assignedWorkType, "") !== workType);
  if (mismatch) {
    return { error: `${mismatch.fullName} uchun biriktirilgan ishlov turi ${workTypeLabel(workType)} emas.` };
  }

  const financeSettings = await getFinanceSettings();
  const ratePerBrick = Math.max(
    0,
    roundMoney(
      typeof body.ratePerBrick !== "undefined"
        ? body.ratePerBrick
        : financeSettings.workRates?.[workType] || 0,
    ),
  );

  if (ratePerBrick <= 0) {
    return { error: `${workTypeLabel(workType)} uchun stavka hali kiritilmagan.` };
  }

  const totalAmount = roundMoney(quantity * ratePerBrick);
  const shareAmount = roundMoney(totalAmount / workers.length);

  return {
    value: {
      date,
      workType,
      quantity,
      ratePerBrick,
      totalAmount,
      shareAmount,
      workerIds: workers.map((item) => item._id),
      notes,
    },
  };
}

async function handleWorkLogList(request, response, urlObject) {
  const auth = await requireAuth(request, response, ["admin", "organizer", "worker"]);
  if (!auth) {
    return;
  }

  const workType = normalizeWorkType(urlObject.searchParams.get("workType"), "");
  const date = safeString(urlObject.searchParams.get("date"), 10);
  const monthKey = safeString(urlObject.searchParams.get("monthKey"), 7);
  const mine = parseBoolean(urlObject.searchParams.get("mine"), false);
  const query = {};

  if (workType) {
    query.workType = workType;
  }
  if (date) {
    query.date = date;
  }
  if (auth.user.role === "worker" || mine) {
    query.workerIds = auth.user._id;
  }

  let items = await collections.workLogs.find(query).sort({ date: -1, createdAt: -1 }).limit(200).toArray();
  if (monthKey) {
    items = items.filter((item) => safeString(item.date, 7) === monthKey);
  }

  sendJson(response, 200, { items: await enrichWorkLogs(items) });
}

async function handleWorkLogCreate(request, response) {
  const auth = await requireAuth(request, response, ["admin", "organizer"]);
  if (!auth) {
    return;
  }

  const body = await readBody(request);
  const validation = await validateWorkLogInput(body);
  if (validation.error) {
    return sendJson(response, 400, { error: validation.error });
  }

  const now = new Date();
  const payload = {
    ...validation.value,
    createdBy: auth.user._id,
    createdAt: now,
    updatedAt: now,
  };

  const result = await collections.workLogs.insertOne(payload);
  await createNotificationBatch(payload.workerIds, {
    type: "work_log_added",
    title: "Ish haqi yozuvi qo'shildi",
    body: `${workTypeLabel(payload.workType)} bo'yicha ${payload.quantity} ta yozuv qo'shildi.`,
    link: "/worker.html",
    meta: { date: payload.date, workType: payload.workType, shareAmount: payload.shareAmount },
  });
  const [item] = await enrichWorkLogs([{ ...payload, _id: result.insertedId }]);
  sendJson(response, 201, { ok: true, item });
}

async function handleWorkLogDelete(request, response, id) {
  const auth = await requireAuth(request, response, ["admin"]);
  if (!auth) {
    return;
  }

  if (!ObjectId.isValid(id)) {
    return sendJson(response, 400, { error: "Ish haqi yozuvi ID noto'g'ri." });
  }

  const result = await collections.workLogs.deleteOne({ _id: new ObjectId(id) });
  if (!result.deletedCount) {
    return sendJson(response, 404, { error: "Ish haqi yozuvi topilmadi." });
  }

  sendJson(response, 200, { ok: true });
}

async function validateWorkerTransactionInput(body) {
  if (!ObjectId.isValid(body.workerId)) {
    return { error: "Ishchi tanlanmadi." };
  }

  const worker = await collections.users.findOne({ _id: new ObjectId(body.workerId), role: "worker" });
  if (!worker) {
    return { error: "Ishchi topilmadi." };
  }

  const amount = roundMoney(body.amount || 0);
  if (!Number.isFinite(amount) || amount <= 0) {
    return { error: "Summa noto'g'ri." };
  }

  return {
    worker,
    value: {
      workerId: worker._id,
      type: normalizeWorkerTransactionType(body.type, "advance"),
      amount,
      date: safeString(body.date, 10) || getYmd(),
      note: safeString(body.note, 300),
    },
  };
}

async function handleWorkerAccountsList(request, response, urlObject) {
  const auth = await requireAuth(request, response, ["admin"]);
  if (!auth) {
    return;
  }

  const monthKey = safeString(urlObject.searchParams.get("monthKey"), 7) || toMonthKey();
  const status = safeString(urlObject.searchParams.get("status"), 20);
  const users = await collections.users.find({ role: "worker", isActive: true }).sort({ createdAt: 1 }).toArray();
  const items = (await buildPayrollSnapshots({ monthKey, users }))
    .filter((item) => filterWorkerAccountByStatus(item, status))
    .sort((left, right) => {
      if (right.debtAmount !== left.debtAmount) {
        return right.debtAmount - left.debtAmount;
      }
      if (right.payableAmount !== left.payableAmount) {
        return right.payableAmount - left.payableAmount;
      }
      return String(left.user?.fullName || "").localeCompare(String(right.user?.fullName || ""));
    });
  const recentTransactionsRaw = await collections.workerTransactions.find({}).sort({ date: -1, createdAt: -1 }).limit(30).toArray();

  sendJson(response, 200, {
    monthKey,
    items,
    recentTransactions: await enrichWorkerTransactions(recentTransactionsRaw),
  });
}

async function handleWorkerTransactionCreate(request, response) {
  const auth = await requireAuth(request, response, ["admin"]);
  if (!auth) {
    return;
  }

  const body = await readBody(request);
  const validation = await validateWorkerTransactionInput(body);
  if (validation.error) {
    return sendJson(response, 400, { error: validation.error });
  }

  const now = new Date();
  const payload = {
    ...validation.value,
    createdBy: auth.user._id,
    createdAt: now,
    updatedAt: now,
  };

  const result = await collections.workerTransactions.insertOne(payload);
  await createNotification({
    userId: validation.worker._id,
    type: "worker_balance_entry",
    title: "Hisobingizga yangi yozuv qo'shildi",
    body: `${workerTransactionMeta(payload.type).label}: ${payload.amount} so'm.`,
    link: "/profile.html",
    meta: { type: payload.type, amount: payload.amount, date: payload.date },
  });

  const [item] = await enrichWorkerTransactions([{ ...payload, _id: result.insertedId }]);
  sendJson(response, 201, { ok: true, item });
}

async function handleWorkerTransactionDelete(request, response, id) {
  const auth = await requireAuth(request, response, ["admin"]);
  if (!auth) {
    return;
  }

  if (!ObjectId.isValid(id)) {
    return sendJson(response, 400, { error: "Yozuv ID noto'g'ri." });
  }

  const result = await collections.workerTransactions.deleteOne({ _id: new ObjectId(id) });
  if (!result.deletedCount) {
    return sendJson(response, 404, { error: "Yozuv topilmadi." });
  }

  sendJson(response, 200, { ok: true });
}

async function handleCustomerAccountsList(request, response, urlObject) {
  const auth = await requireAuth(request, response, ["admin", "organizer"]);
  if (!auth) {
    return;
  }

  const status = safeString(urlObject.searchParams.get("status"), 20) || "all";
  const data = await buildCustomerAccounts(status);
  sendJson(response, 200, data);
}

async function handleCustomerPaymentCreate(request, response) {
  const auth = await requireAuth(request, response, ["admin", "organizer"]);
  if (!auth) {
    return;
  }

  const body = await readBody(request);
  if (!ObjectId.isValid(body.taskId)) {
    return sendJson(response, 400, { error: "Buyurtma tanlanmadi." });
  }

  const task = await collections.tasks.findOne({ _id: new ObjectId(body.taskId), type: "delivery" });
  if (!task) {
    return sendJson(response, 404, { error: "Buyurtma topilmadi." });
  }

  const amount = roundMoney(body.amount || 0);
  if (!Number.isFinite(amount) || amount <= 0) {
    return sendJson(response, 400, { error: "To'lov summasi noto'g'ri." });
  }

  const financeSettings = await getFinanceSettings();
  const paymentTotals = await getTaskPaymentTotalsMap([task._id]);
  const snapshot = buildTaskPaymentSnapshot(task, paymentTotals.get(normalizeIdString(task._id)) || 0, financeSettings);
  if (amount > snapshot.remainingAmount) {
    return sendJson(response, 400, { error: "Kiritilgan summa qolgan qarzdan katta." });
  }

  const now = new Date();
  const payload = {
    taskId: task._id,
    customerName: task.customerName,
    amount,
    date: safeString(body.date, 10) || getYmd(),
    note: safeString(body.note, 300),
    createdBy: auth.user._id,
    createdAt: now,
    updatedAt: now,
  };

  const result = await collections.customerPayments.insertOne(payload);
  sendJson(response, 201, {
    ok: true,
    payment: {
      id: normalizeIdString(result.insertedId),
      taskId: normalizeIdString(task._id),
      customerName: task.customerName,
      amount,
      date: payload.date,
      note: payload.note,
    },
  });
}

async function handleTaskCreate(request, response) {
  const auth = await requireAuth(request, response, ["admin", "organizer"]);
  if (!auth) {
    return;
  }

  const body = await readBody(request);
  const validation = validateTaskInput(body);

  if (validation.error) {
    return sendJson(response, 400, { error: validation.error });
  }

  const now = new Date();
  const financeSettings = await getFinanceSettings();
  const task = {
    ...validation.value,
    unitPrice: validation.value.type === "delivery"
      ? Math.max(0, roundMoney(body.unitPrice || financeSettings.salePricePerBrick || 0))
      : 0,
    status: "planned",
    createdBy: auth.user._id,
    progressNotes: [],
    createdAt: now,
    updatedAt: now,
  };

  const result = await collections.tasks.insertOne(task);
  const workers = await collections.users.find({ role: "worker", isActive: true }).toArray();
  await createNotificationBatch(workers.map((item) => item._id), {
    type: "task_created",
    title: "Yangi topshiriq qo'shildi",
    body: `${task.customerName} uchun ${task.quantity} ta topshiriq rejalashtirildi.`,
    link: "/worker.html",
    meta: { taskType: task.type, scheduledDate: task.scheduledDate },
  });
  const created = await enrichTasks([{ ...task, _id: result.insertedId }]);
  sendJson(response, 201, { ok: true, task: created[0] });
}

async function handleTaskList(request, response, urlObject) {
  const auth = await requireAuth(request, response, ["admin", "organizer", "worker"]);
  if (!auth) {
    return;
  }

  const type = safeString(urlObject.searchParams.get("type"), 20);
  const status = safeString(urlObject.searchParams.get("status"), 20);
  const scheduledDate = safeString(urlObject.searchParams.get("scheduledDate"), 20);
  const mine = parseBoolean(urlObject.searchParams.get("mine"), false);

  const query = {};

  if (["production", "delivery"].includes(type)) {
    query.type = type;
  }
  if (["planned", "accepted", "in_progress", "done"].includes(status)) {
    query.status = status;
  }
  if (scheduledDate) {
    query.scheduledDate = scheduledDate;
  }

  if (auth.user.role === "worker" && mine) {
    query.acceptedBy = auth.user._id;
  }

  const tasks = await collections.tasks.find(query).sort({ scheduledDate: 1, createdAt: -1 }).limit(200).toArray();
  sendJson(response, 200, { tasks: await enrichTasks(tasks) });
}

async function handleTaskAccept(request, response, id) {
  const auth = await requireAuth(request, response, ["worker", "admin"]);
  if (!auth) {
    return;
  }

  if (!ObjectId.isValid(id)) {
    return sendJson(response, 400, { error: "Task ID noto'g'ri." });
  }

  const task = await collections.tasks.findOne({ _id: new ObjectId(id) });
  if (!task) {
    return sendJson(response, 404, { error: "Topshiriq topilmadi." });
  }

  if (
    task.acceptedBy &&
    normalizeIdString(task.acceptedBy) !== normalizeIdString(auth.user._id) &&
    auth.user.role !== "admin"
  ) {
    return sendJson(response, 409, { error: "Bu topshiriq boshqa ishchi tomonidan olingan." });
  }

  const now = new Date();
  const update = {
    acceptedBy: auth.user._id,
    acceptedAt: task.acceptedAt || now,
    status: task.status === "done" ? "done" : "accepted",
    updatedAt: now,
    progressNotes: [
      ...(task.progressNotes || []),
      { note: "Topshiriq qabul qilindi", status: "accepted", at: now, byRole: auth.user.role },
    ],
  };

  await collections.tasks.updateOne({ _id: task._id }, { $set: update });
  if (task.createdBy && normalizeIdString(task.createdBy) !== normalizeIdString(auth.user._id)) {
    await createNotification({
      userId: task.createdBy,
      type: "task_accepted",
      title: "Topshiriq qabul qilindi",
      body: `${task.customerName} buyurtmasi bo'yicha topshiriq qabul qilindi.`,
      link: "/dashboard",
      meta: { taskId: normalizeIdString(task._id) },
    });
  }
  const updatedTask = await collections.tasks.findOne({ _id: task._id });
  const enriched = await enrichTasks([updatedTask]);
  sendJson(response, 200, { ok: true, task: enriched[0] });
}

async function handleTaskStatusUpdate(request, response, id) {
  const auth = await requireAuth(request, response, ["worker", "organizer", "admin"]);
  if (!auth) {
    return;
  }

  if (!ObjectId.isValid(id)) {
    return sendJson(response, 400, { error: "Task ID noto'g'ri." });
  }

  const body = await readBody(request);
  const status = safeString(body.status, 20);
  const note = safeString(body.note, 180);

  if (!["planned", "accepted", "in_progress", "done"].includes(status)) {
    return sendJson(response, 400, { error: "Status noto'g'ri." });
  }

  const task = await collections.tasks.findOne({ _id: new ObjectId(id) });
  if (!task) {
    return sendJson(response, 404, { error: "Topshiriq topilmadi." });
  }

  if (
    auth.user.role === "worker" &&
    task.acceptedBy &&
    normalizeIdString(task.acceptedBy) !== normalizeIdString(auth.user._id)
  ) {
    return sendJson(response, 403, { error: "Faqat o'zingiz olgan topshiriqni yangilay olasiz." });
  }

  const now = new Date();
  const update = {
    status,
    updatedAt: now,
  };

  if (!task.acceptedBy && auth.user.role === "worker") {
    update.acceptedBy = auth.user._id;
    update.acceptedAt = now;
  }

  if (status === "done") {
    update.completedBy = auth.user._id;
    update.completedAt = now;
  }

  if (status === "accepted" && !task.acceptedBy) {
    update.acceptedBy = auth.user._id;
    update.acceptedAt = now;
  }

  update.progressNotes = [
    ...(task.progressNotes || []),
    {
      note: note || `Status ${status} ga o'tdi`,
      status,
      at: now,
      byRole: auth.user.role,
    },
  ];

  await collections.tasks.updateOne({ _id: task._id }, { $set: update });
  if (status === "done" && task.createdBy && normalizeIdString(task.createdBy) !== normalizeIdString(auth.user._id)) {
    await createNotification({
      userId: task.createdBy,
      type: "task_done",
      title: "Topshiriq yakunlandi",
      body: `${task.customerName} bo'yicha ${task.quantity} ta topshiriq yakunlandi.`,
      link: "/dashboard",
      meta: { taskId: normalizeIdString(task._id) },
    });
  }
  const updatedTask = await collections.tasks.findOne({ _id: task._id });
  const enriched = await enrichTasks([updatedTask]);
  sendJson(response, 200, { ok: true, task: enriched[0] });
}

async function handleTaskUpdate(request, response, id) {
  const auth = await requireAuth(request, response, ["admin", "organizer"]);
  if (!auth) {
    return;
  }

  if (!ObjectId.isValid(id)) {
    return sendJson(response, 400, { error: "Task ID noto'g'ri." });
  }

  const task = await collections.tasks.findOne({ _id: new ObjectId(id) });
  if (!task) {
    return sendJson(response, 404, { error: "Topshiriq topilmadi." });
  }

  const body = await readBody(request);
  const update = {
    updatedAt: new Date(),
  };

  if (typeof body.type === "string" && ["production", "delivery"].includes(body.type)) {
    update.type = body.type;
  }
  if (typeof body.workType !== "undefined") {
    update.workType = normalizeWorkType(body.workType, "");
  }
  if (typeof body.customerName === "string" && safeString(body.customerName, 120)) {
    update.customerName = safeString(body.customerName, 120);
  }
  if (typeof body.quantity !== "undefined") {
    const quantity = Math.round(Number(body.quantity));
    if (!Number.isFinite(quantity) || quantity <= 0) {
      return sendJson(response, 400, { error: "Miqdor noto'g'ri." });
    }
    update.quantity = quantity;
  }
  if (typeof body.scheduledDate === "string" && safeString(body.scheduledDate, 20)) {
    update.scheduledDate = safeString(body.scheduledDate, 20);
  }
  if (typeof body.notes === "string") {
    update.notes = safeString(body.notes, 500);
  }
  if (typeof body.unitPrice !== "undefined") {
    const unitPrice = roundMoney(body.unitPrice || 0);
    if (!Number.isFinite(unitPrice) || unitPrice < 0) {
      return sendJson(response, 400, { error: "Narx noto'g'ri." });
    }
    update.unitPrice = unitPrice;
  }

  if (Object.keys(update).length === 1) {
    return sendJson(response, 400, { error: "Yangilash uchun ma'lumot yuborilmadi." });
  }

  update.progressNotes = [
    ...(task.progressNotes || []),
    {
      note: "Topshiriq ma'lumotlari tahrirlandi",
      status: task.status,
      at: update.updatedAt,
      byRole: auth.user.role,
    },
  ];

  await collections.tasks.updateOne({ _id: task._id }, { $set: update });
  const updatedTask = await collections.tasks.findOne({ _id: task._id });
  const enriched = await enrichTasks([updatedTask]);
  sendJson(response, 200, { ok: true, task: enriched[0] });
}

async function handleTaskDelete(request, response, id) {
  const auth = await requireAuth(request, response, ["admin"]);
  if (!auth) {
    return;
  }

  if (!ObjectId.isValid(id)) {
    return sendJson(response, 400, { error: "Task ID noto'g'ri." });
  }

  const taskId = new ObjectId(id);
  const paymentCount = await collections.customerPayments.countDocuments({ taskId });
  if (paymentCount > 0) {
    return sendJson(response, 400, {
      error: "Bu buyurtma uchun to'lov tarixi mavjud. O'chirish o'rniga tahrirlash tavsiya qilinadi.",
    });
  }

  const result = await collections.tasks.deleteOne({ _id: taskId });
  if (!result.deletedCount) {
    return sendJson(response, 404, { error: "Topshiriq topilmadi." });
  }

  sendJson(response, 200, { ok: true });
}

async function handleTaskSummary(request, response, urlObject) {
  const auth = await requireAuth(request, response, ["admin", "organizer", "worker"]);
  if (!auth) {
    return;
  }

  const scheduledDate = safeString(urlObject.searchParams.get("scheduledDate"), 20) || getYmd();
  const tasks = await collections.tasks.find({ scheduledDate }).toArray();

  const summary = {
    date: scheduledDate,
    total: tasks.length,
    production: tasks.filter((item) => item.type === "production").length,
    delivery: tasks.filter((item) => item.type === "delivery").length,
    planned: tasks.filter((item) => item.status === "planned").length,
    accepted: tasks.filter((item) => item.status === "accepted").length,
    inProgress: tasks.filter((item) => item.status === "in_progress").length,
    done: tasks.filter((item) => item.status === "done").length,
  };

  sendJson(response, 200, { summary });
}

async function handleContentList(request, response, urlObject) {
  const type = safeString(urlObject.searchParams.get("type"), 20);
  const limit = Math.min(Number(urlObject.searchParams.get("limit") || 20), 50);
  const includeDrafts = parseBoolean(urlObject.searchParams.get("includeDrafts"), false);
  const query = {};

  if (["blog", "news", "product"].includes(type)) {
    query.type = type;
  }

  if (!includeDrafts) {
    query.isPublished = true;
  } else {
    const auth = await requireAuth(request, response, ["admin"]);
    if (!auth) {
      return;
    }
  }

  const items = await collections.contents.find(query).sort({ createdAt: -1 }).limit(limit).toArray();
  sendJson(response, 200, { items: items.map(serializeContent) });
}

async function handleContentCreate(request, response) {
  const auth = await requireAuth(request, response, ["admin"]);
  if (!auth) {
    return;
  }

  const body = await readBody(request);
  const type = safeString(body.type, 20);
  const title = safeString(body.title, 120);
  const excerpt = safeString(body.excerpt, 280);
  const articleBody = safeString(body.body, 5000);
  const priceLabel = safeString(body.priceLabel, 80);
  const isPublished = parseBoolean(body.isPublished, true);
  const tags = parseTags(body.tags);

  if (!["blog", "news", "product"].includes(type)) {
    return sendJson(response, 400, { error: "Content turi noto'g'ri." });
  }

  if (!title || !excerpt || !articleBody) {
    return sendJson(response, 400, { error: "Sarlavha, qisqa matn va asosiy matn majburiy." });
  }

  const imageUrl = await resolveImageUrl({
    imageUrl: body.imageUrl,
    imageBase64: body.imageBase64,
    type,
    title,
  });

  const baseSlug = slugify(title) || `${type}-${Date.now()}`;
  let slug = baseSlug;
  let counter = 1;
  while (await collections.contents.findOne({ slug })) {
    counter += 1;
    slug = `${baseSlug}-${counter}`;
  }

  const now = new Date();
  const item = {
    type,
    title,
    slug,
    excerpt,
    body: articleBody,
    imageUrl,
    priceLabel,
    tags,
    isPublished,
    createdBy: auth.user._id,
    createdAt: now,
    updatedAt: now,
  };

  const result = await collections.contents.insertOne(item);
  sendJson(response, 201, { ok: true, item: serializeContent({ ...item, _id: result.insertedId }) });
}

async function handleContentUpdate(request, response, id) {
  const auth = await requireAuth(request, response, ["admin"]);
  if (!auth) {
    return;
  }

  if (!ObjectId.isValid(id)) {
    return sendJson(response, 400, { error: "Content ID noto'g'ri." });
  }

  const body = await readBody(request);
  const existing = await collections.contents.findOne({ _id: new ObjectId(id) });

  if (!existing) {
    return sendJson(response, 404, { error: "Material topilmadi." });
  }

  const update = {
    updatedAt: new Date(),
  };

  if (typeof body.type === "string" && ["blog", "news", "product"].includes(body.type)) {
    update.type = body.type;
  }
  if (typeof body.title === "string" && safeString(body.title, 120)) {
    update.title = safeString(body.title, 120);
  }
  if (typeof body.excerpt === "string") {
    update.excerpt = safeString(body.excerpt, 280);
  }
  if (typeof body.body === "string") {
    update.body = safeString(body.body, 5000);
  }
  if (typeof body.priceLabel === "string") {
    update.priceLabel = safeString(body.priceLabel, 80);
  }
  if (typeof body.isPublished !== "undefined") {
    update.isPublished = parseBoolean(body.isPublished, existing.isPublished);
  }
  if (typeof body.tags !== "undefined") {
    update.tags = parseTags(body.tags);
  }
  if (body.imageBase64 || body.imageUrl) {
    update.imageUrl = await resolveImageUrl({
      imageUrl: body.imageUrl,
      imageBase64: body.imageBase64,
      type: update.type || existing.type,
      title: update.title || existing.title,
    });
  }

  await collections.contents.updateOne({ _id: existing._id }, { $set: update });
  const updatedItem = await collections.contents.findOne({ _id: existing._id });
  sendJson(response, 200, { ok: true, item: serializeContent(updatedItem) });
}

async function handleContentDelete(request, response, id) {
  const auth = await requireAuth(request, response, ["admin"]);
  if (!auth) {
    return;
  }

  if (!ObjectId.isValid(id)) {
    return sendJson(response, 400, { error: "Content ID noto'g'ri." });
  }

  const result = await collections.contents.deleteOne({ _id: new ObjectId(id) });
  if (!result.deletedCount) {
    return sendJson(response, 404, { error: "Material topilmadi." });
  }

  sendJson(response, 200, { ok: true });
}

async function handleFinanceDashboard(request, response) {
  const auth = await requireAuth(request, response, ["admin"]);
  if (!auth) {
    return;
  }

  sendJson(response, 200, { finance: await buildFinanceDashboardSafe() });
}

async function handleFinanceSettingsUpdate(request, response) {
  const auth = await requireAuth(request, response, ["admin"]);
  if (!auth) {
    return;
  }

  const body = await readBody(request);
  const settings = await updateFinanceSettings(body, auth.user._id);
  await syncAllCameraWorkLogsForDate().catch(() => null);
  sendJson(response, 200, { ok: true, settings });
}

async function resolveRequestedCameraMonitor(urlObject) {
  const system = await getCameraSystemSettings();
  const monitorId = safeString(urlObject.searchParams.get("monitorId"), 40);
  if (monitorId) {
    return system.monitors.find((item) => item.id === monitorId) || null;
  }
  return system.monitors.find((item) => item.enabled) || system.monitors[0] || null;
}

async function handleCameraSettingsGet(request, response) {
  const auth = await requireAuth(request, response, ["admin"]);
  if (!auth) {
    return;
  }

  const system = await getCameraSystemSettings();
  sendJson(response, 200, {
    settings: system.monitors[0] || normalizeCameraMonitor(defaultCameraMonitor(1)),
  });
}

async function handleCameraSettingsUpdate(request, response) {
  const auth = await requireAuth(request, response, ["admin"]);
  if (!auth) {
    return;
  }

  try {
    const body = await readBody(request);
    const settings = await updateCameraSettings(body, auth.user._id);
    await reloadCameraMonitorService();
    sendJson(response, 200, { ok: true, settings });
  } catch (error) {
    sendJson(response, 400, { error: error.message || "Kamera sozlamasi yangilanmadi." });
  }
}

async function handleCameraMonitorsList(request, response, urlObject) {
  const auth = await requireAuth(request, response, ["admin"]);
  if (!auth) {
    return;
  }

  const date = safeString(urlObject.searchParams.get("date"), 10) || getYmd();
  sendJson(response, 200, {
    items: await buildCameraMonitorsPayload(date),
    date,
  });
}

async function handleCameraMonitorCreate(request, response) {
  const auth = await requireAuth(request, response, ["admin"]);
  if (!auth) {
    return;
  }

  try {
    const body = await readBody(request);
    const item = await createCameraMonitor(body, auth.user._id);
    await reloadCameraMonitorService();
    sendJson(response, 201, { ok: true, item });
  } catch (error) {
    sendJson(response, 400, { error: error.message || "Kamera yaratilmadi." });
  }
}

async function handleCameraMonitorUpdate(request, response, id) {
  const auth = await requireAuth(request, response, ["admin"]);
  if (!auth) {
    return;
  }

  try {
    const body = await readBody(request);
    const item = await updateCameraMonitor(id, body, auth.user._id);
    await reloadCameraMonitorService();
    sendJson(response, 200, { ok: true, item });
  } catch (error) {
    sendJson(response, 400, { error: error.message || "Kamera yangilanmadi." });
  }
}

async function handleCameraMonitorDelete(request, response, id) {
  const auth = await requireAuth(request, response, ["admin"]);
  if (!auth) {
    return;
  }

  try {
    const item = await deleteCameraMonitor(id, auth.user._id);
    await reloadCameraMonitorService();
    sendJson(response, 200, { ok: true, item });
  } catch (error) {
    sendJson(response, 400, { error: error.message || "Kamera o'chirilmadi." });
  }
}

async function handleCameraMonitorReset(request, response, id, urlObject) {
  const auth = await requireAuth(request, response, ["admin"]);
  if (!auth) {
    return;
  }

  const date = safeString(urlObject.searchParams.get("date"), 10) || getYmd();
  const item = await resetCameraCounterForDate(id, date);
  if (!item) {
    return sendJson(response, 404, { error: "Counter topilmadi." });
  }
  sendJson(response, 200, { ok: true, item });
}

async function handleCameraFrame(request, response, urlObject) {
  const auth = await requireAuth(request, response, ["admin"]);
  if (!auth) {
    return;
  }

  const monitor = await resolveRequestedCameraMonitor(urlObject);
  if (!monitor) {
    return sendJson(response, 404, { error: "Kamera topilmadi." });
  }
  if (!monitor.enabled) {
    return sendJson(response, 400, { error: "Kamera paneli hali yoqilmagan." });
  }

  try {
    const frame = await fetchCameraFrame(monitor);
    return sendBuffer(response, 200, frame.buffer, frame.contentType, {
      "Cache-Control": "no-store, max-age=0",
    });
  } catch (error) {
    return sendJson(response, 502, { error: error.message || "Kamera frame olib bo'lmadi." });
  }
}

async function handleDemoCameraFrame(response, multipart = false) {
  const buffer = await renderDemoCameraFrameBuffer();
  if (multipart) {
    const header = Buffer.from(`--frame\r\nContent-Type: image/jpeg\r\nContent-Length: ${buffer.length}\r\n\r\n`, "utf8");
    const footer = Buffer.from("\r\n--frame--\r\n", "utf8");
    response.writeHead(200, {
      "Content-Type": "multipart/x-mixed-replace; boundary=frame",
      "Cache-Control": "no-store",
    });
    response.end(Buffer.concat([header, buffer, footer]));
    return;
  }
  return sendBuffer(response, 200, buffer, "image/jpeg", {
    "Cache-Control": "no-store, max-age=0",
  });
}

async function handleProductionSummary(request, response, urlObject) {
  const auth = await requireAuth(request, response, ["admin", "organizer", "worker"]);
  if (!auth) {
    return;
  }

  const date = safeString(urlObject.searchParams.get("date"), 10) || getYmd();
  const mine = parseBoolean(urlObject.searchParams.get("mine"), false);
  const summary = await buildProductionSummary(date, mine ? auth.user : auth.user.role === "worker" ? auth.user : null);
  return sendJson(response, 200, summary);
}

async function handlePayrollList(request, response, urlObject) {
  const auth = await requireAuth(request, response, ["admin", "organizer", "worker"]);
  if (!auth) {
    return;
  }

  await ensureBusinessState();
  const monthKey = safeString(urlObject.searchParams.get("monthKey"), 7) || toMonthKey();
  const mine = parseBoolean(urlObject.searchParams.get("mine"), false);
  let users = [];

  if (auth.user.role === "admin" && !mine) {
    users = await collections.users.find({ isActive: true }).sort({ createdAt: 1 }).toArray();
  } else {
    users = [auth.user];
  }

  const items = (await buildPayrollSnapshots({ monthKey, users }))
    .sort((left, right) => {
      if (right.debtAmount !== left.debtAmount) {
        return right.debtAmount - left.debtAmount;
      }
      if (right.payableAmount !== left.payableAmount) {
        return right.payableAmount - left.payableAmount;
      }
      return String(left.user?.fullName || "").localeCompare(String(right.user?.fullName || ""));
    });

  sendJson(response, 200, {
    monthKey,
    items,
    summary: {
      totalAmount: roundMoney(items.reduce((sum, item) => sum + item.accruedAmount, 0)),
      paidAmount: roundMoney(items.reduce((sum, item) => sum + item.paidAmount, 0)),
      unpaidAmount: roundMoney(items.reduce((sum, item) => sum + item.payableAmount, 0)),
      debtAmount: roundMoney(items.reduce((sum, item) => sum + item.debtAmount, 0)),
      paidCount: items.filter((item) => item.status === "paid").length,
      unpaidCount: items.filter((item) => item.payableAmount > 0).length,
    },
  });
}

async function handlePayrollPay(request, response, id) {
  const auth = await requireAuth(request, response, ["admin"]);
  if (!auth) {
    return;
  }

  const parsedId = parsePayrollIdentifier(id);
  if (!parsedId) {
    return sendJson(response, 400, { error: "Payroll ID noto'g'ri." });
  }

  const body = await readBody(request);
  let payroll = null;
  let userId = "";
  let monthKey = "";

  if (parsedId.kind === "objectId") {
    payroll = await collections.payrolls.findOne({ _id: new ObjectId(parsedId.id) });
    if (!payroll) {
      return sendJson(response, 404, { error: "Oylik yozuvi topilmadi." });
    }
    userId = normalizeIdString(payroll.userId);
    monthKey = payroll.monthKey;
  } else {
    userId = parsedId.userId;
    monthKey = parsedId.monthKey;
    payroll = await collections.payrolls.findOne({ userId: new ObjectId(userId), monthKey });
  }

  const user = await collections.users.findOne({ _id: new ObjectId(userId) });
  if (!user) {
    return sendJson(response, 404, { error: "Foydalanuvchi topilmadi." });
  }

  const currentSnapshot = await getPayrollSnapshotForUser(user, monthKey);
  if (currentSnapshot.payableAmount <= 0) {
    return sendJson(response, 400, {
      error: currentSnapshot.debtAmount > 0
        ? "Bu oy uchun to'lanadigan summa yo'q, faqat qarz balansi mavjud."
        : "Bu oy uchun to'lanadigan summa qolmagan.",
    });
  }

  const now = new Date();
  const payload = {
    userId: user._id,
    monthKey,
    dueDate: currentSnapshot.dueDate,
    amount: currentSnapshot.payableAmount,
    status: "paid",
    paidAt: now,
    notes: safeString(body.notes, 300),
    updatedAt: now,
  };

  if (payroll) {
    await collections.payrolls.updateOne({ _id: payroll._id }, { $set: payload });
  } else {
    const result = await collections.payrolls.insertOne({
      ...payload,
      createdAt: now,
    });
    payroll = { ...payload, _id: result.insertedId };
  }

  await createNotification({
    userId: user._id,
    type: "salary_paid",
    title: "Oylik tushdi",
    body: `${monthKey} hisob-kitobi bo'yicha ${currentSnapshot.payableAmount} so'm to'lov tasdiqlandi.`,
    link: "/profile.html",
    meta: { monthKey, payrollId: normalizeIdString(payroll._id) },
  });

  sendJson(response, 200, { ok: true, item: await getPayrollSnapshotForUser(user, monthKey) });
}

async function handleNotificationsList(request, response, urlObject) {
  const auth = await requireAuth(request, response, ["admin", "organizer", "worker"]);
  if (!auth) {
    return;
  }

  await ensureBusinessState();
  const limit = Math.min(Math.max(parseNumber(urlObject.searchParams.get("limit"), 20), 1), 100);
  const unreadOnly = parseBoolean(urlObject.searchParams.get("unreadOnly"), false);
  const scope = safeString(urlObject.searchParams.get("scope"), 20);
  const query = {};

  if (!(auth.user.role === "admin" && scope === "all")) {
    query.userId = auth.user._id;
  }

  const items = await collections.notifications.find(query).sort({ createdAt: -1 }).limit(limit).toArray();
  const filtered = unreadOnly ? items.filter((item) => !item.readAt) : items;
  const userMap = await getUserMapByIds(filtered.map((item) => item.userId));
  const notifications = filtered.map((item) => serializeNotification(item, userMap));
  sendJson(response, 200, {
    notifications,
    unreadCount: notifications.filter((item) => !item.isRead).length,
  });
}

async function handleNotificationCreate(request, response) {
  const auth = await requireAuth(request, response, ["admin"]);
  if (!auth) {
    return;
  }

  const body = await readBody(request);
  const targetType = safeString(body.targetType, 20);
  const role = safeString(body.role, 20);
  const title = safeString(body.title, 120);
  const notificationBody = safeString(body.body, 600);
  const type = safeString(body.type, 40) || "manual";
  const link = safeString(body.link, 200) || "/profile.html";

  if (!title || !notificationBody) {
    return sendJson(response, 400, { error: "Sarlavha va matn majburiy." });
  }

  let recipients = [];
  if (targetType === "user" && ObjectId.isValid(body.userId)) {
    const user = await collections.users.findOne({ _id: new ObjectId(body.userId), isActive: true });
    recipients = user ? [user._id] : [];
  } else if (targetType === "role" && ["admin", "organizer", "worker"].includes(role)) {
    recipients = (await collections.users.find({ role, isActive: true }).toArray()).map((user) => user._id);
  } else if (targetType === "all") {
    recipients = (await collections.users.find({ isActive: true }).toArray()).map((user) => user._id);
  } else {
    return sendJson(response, 400, { error: "Xabarnoma qabul qiluvchisi noto'g'ri." });
  }

  if (!recipients.length) {
    return sendJson(response, 400, { error: "Xabarnoma uchun qabul qiluvchi topilmadi." });
  }

  const created = await createNotificationBatch(recipients, {
    title,
    body: notificationBody,
    type,
    link,
    meta: { senderRole: auth.user.role, targetType, role },
  });

  sendJson(response, 201, { ok: true, count: created.length });
}

async function handleNotificationRead(request, response, id) {
  const auth = await requireAuth(request, response, ["admin", "organizer", "worker"]);
  if (!auth) {
    return;
  }

  if (!ObjectId.isValid(id)) {
    return sendJson(response, 400, { error: "Notification ID noto'g'ri." });
  }

  const notification = await collections.notifications.findOne({ _id: new ObjectId(id) });
  if (!notification) {
    return sendJson(response, 404, { error: "Xabarnoma topilmadi." });
  }

  if (auth.user.role !== "admin" && normalizeIdString(notification.userId) !== normalizeIdString(auth.user._id)) {
    return sendJson(response, 403, { error: "Bu xabarnomaga ruxsat yo'q." });
  }

  await collections.notifications.updateOne(
    { _id: notification._id },
    { $set: { readAt: new Date(), updatedAt: new Date() } },
  );

  sendJson(response, 200, { ok: true });
}

async function buildRoleProfileSummary(user) {
  const production = await buildProductionSummary(getYmd(), user.role === "worker" ? user : null);

  if (user.role === "worker") {
    const [tasks, payroll, workLogs] = await Promise.all([
      collections.tasks.find({ acceptedBy: user._id }).toArray(),
      getPayrollSnapshotForUser(user, toMonthKey()),
      collections.workLogs.find({ workerIds: user._id }).toArray(),
    ]);
    return {
      totalAssigned: tasks.length,
      doneCount: tasks.filter((item) => item.status === "done").length,
      activeCount: tasks.filter((item) => item.status !== "done").length,
      thisMonthBatches: workLogs.filter((item) => safeString(item.date, 7) === toMonthKey()).length,
      payableAmount: payroll.payableAmount,
      debtAmount: payroll.debtAmount,
      todayQuantity: production.mine?.todayQuantity || 0,
      todayAmount: production.mine?.todayAmount || 0,
    };
  }

  if (user.role === "organizer") {
    const tasks = await collections.tasks.find({ createdBy: user._id }).toArray();
    return {
      plannedByMe: tasks.length,
      doneCount: tasks.filter((item) => item.status === "done").length,
      activeCount: tasks.filter((item) => item.status !== "done").length,
      cameraManagedTypes: production.totals.workTypeCount || 0,
      todayProductionQuantity: production.totals.loggedQuantity || 0,
      todayProductionAmount: production.totals.totalAmount || 0,
    };
  }

  const overview = await getOverview();
  return {
    ...overview,
    cameraManagedTypes: production.totals.workTypeCount || 0,
    todayProductionQuantity: production.totals.loggedQuantity || 0,
    todayProductionAmount: production.totals.totalAmount || 0,
  };
}

async function handleProfileGet(request, response) {
  const auth = await requireAuth(request, response, ["admin", "organizer", "worker"]);
  if (!auth) {
    return;
  }

  await ensureBusinessState();
  const monthKey = toMonthKey();
  const [payroll, notifications, roleSummary, productionSummary] = await Promise.all([
    getPayrollSnapshotForUser(auth.user, monthKey),
    collections.notifications.find({ userId: auth.user._id }).sort({ createdAt: -1 }).limit(6).toArray(),
    buildRoleProfileSummary(auth.user),
    buildProductionSummary(getYmd(), auth.user.role === "worker" ? auth.user : null),
  ]);

  const userMap = await getUserMapByIds([auth.user._id]);
  sendJson(response, 200, {
    user: serializeUser(auth.user),
    dashboardPath: mapDashboardPath(auth.user.role),
    roleSummary,
    productionSummary,
    payroll: payroll || null,
    notifications: notifications.map((item) => serializeNotification(item, userMap)),
  });
}

async function handleProfileUpdate(request, response) {
  const auth = await requireAuth(request, response, ["admin", "organizer", "worker"]);
  if (!auth) {
    return;
  }

  const body = await readBody(request);
  const update = {
    updatedAt: new Date(),
  };

  if (typeof body.fullName === "string" && safeString(body.fullName, 80)) {
    update.fullName = safeString(body.fullName, 80);
  }
  if (typeof body.phone === "string") {
    update.phone = safeString(body.phone, 40);
  }
  if (typeof body.positionTitle === "string") {
    update.positionTitle = normalizePositionTitle(auth.user.role, body.positionTitle);
  }
  if (typeof body.bio === "string") {
    update.bio = safeString(body.bio, 500);
  }
  if (typeof body.avatarUrl === "string") {
    update.avatarUrl = safeString(body.avatarUrl, 4000);
  }
  if (typeof body.password === "string" && body.password.trim().length >= 6) {
    update.passwordHash = await hashPassword(body.password.trim());
  }

  await collections.users.updateOne({ _id: auth.user._id }, { $set: update });
  const updated = await collections.users.findOne({ _id: auth.user._id });
  sendJson(response, 200, { ok: true, user: serializeUser(updated) });
}

async function handleUpload(request, response) {
  const auth = await requireAuth(request, response, ["admin"]);
  if (!auth) {
    return;
  }

  const body = await readBody(request);
  const imageBase64 = safeString(body.imageBase64, 9_500_000);
  const folder = safeString(body.folder, 120) || "gisht-platform/uploads";

  if (!imageBase64) {
    return sendJson(response, 400, { error: "Rasm yuborilmadi." });
  }

  const imageUrl = await uploadToCloudinary(imageBase64, folder);
  sendJson(response, 200, { ok: true, imageUrl, cloudinaryEnabled: hasCloudinaryConfig() });
}

async function handleOverview(request, response) {
  const auth = await requireAuth(request, response, ["admin", "organizer", "worker"]);
  if (!auth) {
    return;
  }

  try {
    await ensureBusinessState();
    const currentMonthKey = toMonthKey();
    const [overview, todaySummary, unreadNotifications, currentPayroll] = await Promise.all([
      getOverview(),
      collections.tasks.find({ scheduledDate: getYmd() }).toArray(),
      collections.notifications.countDocuments({ userId: auth.user._id, readAt: null }),
      getPayrollSnapshotForUser(auth.user, currentMonthKey),
    ]);

    const myAssigned = auth.user.role === "worker"
      ? todaySummary.filter((task) => normalizeIdString(task.acceptedBy) === normalizeIdString(auth.user._id)).length
      : 0;

    return sendJson(response, 200, {
      overview: {
        ...overview,
        todayTasks: todaySummary.length,
        myAssigned,
        unreadNotifications,
        currentPayrollAmount: currentPayroll ? roundMoney(currentPayroll.payableAmount || currentPayroll.amount || 0) : 0,
        currentPayrollStatus: currentPayroll?.status || "scheduled",
      },
    });
  } catch (error) {
    console.error("Overview xatosi:", error);
    return sendJson(response, 200, {
      overview: buildOverviewFallback(),
      degraded: true,
    });
  }
}

async function handleApi(request, response, urlObject) {
  const { pathname } = urlObject;

  if (pathname === "/api/health" && request.method === "GET") {
    return sendJson(response, 200, {
      ok: true,
      date: new Date().toISOString(),
      storageMode,
      dbName: DB_NAME,
    });
  }

  if (pathname === "/api/demo/camera.jpg" && request.method === "GET") {
    return handleDemoCameraFrame(response, false);
  }

  if (pathname === "/api/demo/camera.mjpeg" && request.method === "GET") {
    return handleDemoCameraFrame(response, true);
  }

  if (pathname === "/api/site/home" && request.method === "GET") {
    return sendJson(response, 200, await buildHomePayload());
  }

  if (pathname === "/api/auth/me" && request.method === "GET") {
    return handleAuthMe(request, response);
  }

  if (pathname === "/api/auth/login" && request.method === "POST") {
    return handleLogin(request, response);
  }

  if (pathname === "/api/auth/logout" && request.method === "POST") {
    return handleLogout(request, response);
  }

  if (pathname === "/api/users" && request.method === "GET") {
    return handleUsersList(request, response);
  }

  if (pathname === "/api/users" && request.method === "POST") {
    return handleUserCreate(request, response);
  }

  if (pathname.startsWith("/api/users/") && request.method === "PATCH") {
    const id = pathname.split("/").pop();
    return handleUserUpdate(request, response, id);
  }

  if (pathname.startsWith("/api/users/") && request.method === "DELETE") {
    const id = pathname.split("/").pop();
    return handleUserDelete(request, response, id);
  }

  if (pathname === "/api/tasks" && request.method === "GET") {
    return handleTaskList(request, response, urlObject);
  }

  if (pathname === "/api/tasks" && request.method === "POST") {
    return handleTaskCreate(request, response);
  }

  if (pathname === "/api/work-logs" && request.method === "GET") {
    return handleWorkLogList(request, response, urlObject);
  }

  if (pathname === "/api/work-logs" && request.method === "POST") {
    return handleWorkLogCreate(request, response);
  }

  if (pathname.startsWith("/api/work-logs/") && request.method === "DELETE") {
    const id = pathname.split("/").pop();
    return handleWorkLogDelete(request, response, id);
  }

  if (pathname === "/api/worker-accounts" && request.method === "GET") {
    return handleWorkerAccountsList(request, response, urlObject);
  }

  if (pathname === "/api/worker-transactions" && request.method === "POST") {
    return handleWorkerTransactionCreate(request, response);
  }

  if (pathname.startsWith("/api/worker-transactions/") && request.method === "DELETE") {
    const id = pathname.split("/").pop();
    return handleWorkerTransactionDelete(request, response, id);
  }

  if (pathname === "/api/customer-accounts" && request.method === "GET") {
    return handleCustomerAccountsList(request, response, urlObject);
  }

  if (pathname === "/api/customer-payments" && request.method === "POST") {
    return handleCustomerPaymentCreate(request, response);
  }

  if (pathname === "/api/tasks/summary" && request.method === "GET") {
    return handleTaskSummary(request, response, urlObject);
  }

  if (pathname.startsWith("/api/tasks/") && pathname.endsWith("/accept") && request.method === "PATCH") {
    const parts = pathname.split("/");
    return handleTaskAccept(request, response, parts[3]);
  }

  if (pathname.startsWith("/api/tasks/") && pathname.endsWith("/status") && request.method === "PATCH") {
    const parts = pathname.split("/");
    return handleTaskStatusUpdate(request, response, parts[3]);
  }

  if (pathname.startsWith("/api/tasks/") && request.method === "PATCH") {
    const parts = pathname.split("/");
    if (parts.length === 4) {
      return handleTaskUpdate(request, response, parts[3]);
    }
  }

  if (pathname.startsWith("/api/tasks/") && request.method === "DELETE") {
    const id = pathname.split("/").pop();
    return handleTaskDelete(request, response, id);
  }

  if (pathname === "/api/content" && request.method === "GET") {
    return handleContentList(request, response, urlObject);
  }

  if (pathname === "/api/content" && request.method === "POST") {
    return handleContentCreate(request, response);
  }

  if (pathname.startsWith("/api/content/") && request.method === "PATCH") {
    const id = pathname.split("/").pop();
    return handleContentUpdate(request, response, id);
  }

  if (pathname.startsWith("/api/content/") && request.method === "DELETE") {
    const id = pathname.split("/").pop();
    return handleContentDelete(request, response, id);
  }

  if (pathname === "/api/uploads/image" && request.method === "POST") {
    return handleUpload(request, response);
  }

  if (pathname === "/api/finance/dashboard" && request.method === "GET") {
    return handleFinanceDashboard(request, response);
  }

  if (pathname === "/api/finance/settings" && request.method === "PATCH") {
    return handleFinanceSettingsUpdate(request, response);
  }

  if (pathname === "/api/camera/settings" && request.method === "GET") {
    return handleCameraSettingsGet(request, response);
  }

  if (pathname === "/api/camera/settings" && request.method === "PATCH") {
    return handleCameraSettingsUpdate(request, response);
  }

  if (pathname === "/api/camera/frame" && request.method === "GET") {
    return handleCameraFrame(request, response, urlObject);
  }

  if (pathname === "/api/cameras" && request.method === "GET") {
    return handleCameraMonitorsList(request, response, urlObject);
  }

  if (pathname === "/api/cameras" && request.method === "POST") {
    return handleCameraMonitorCreate(request, response);
  }

  if (pathname.startsWith("/api/cameras/") && pathname.endsWith("/reset") && request.method === "POST") {
    const parts = pathname.split("/");
    return handleCameraMonitorReset(request, response, parts[3], urlObject);
  }

  if (pathname.startsWith("/api/cameras/") && request.method === "PATCH") {
    const parts = pathname.split("/");
    return handleCameraMonitorUpdate(request, response, parts[3]);
  }

  if (pathname.startsWith("/api/cameras/") && request.method === "DELETE") {
    const parts = pathname.split("/");
    return handleCameraMonitorDelete(request, response, parts[3]);
  }

  if (pathname === "/api/production-summary" && request.method === "GET") {
    return handleProductionSummary(request, response, urlObject);
  }

  if (pathname === "/api/payroll" && request.method === "GET") {
    return handlePayrollList(request, response, urlObject);
  }

  if (pathname.startsWith("/api/payroll/") && pathname.endsWith("/pay") && request.method === "PATCH") {
    const parts = pathname.split("/");
    return handlePayrollPay(request, response, parts[3]);
  }

  if (pathname === "/api/notifications" && request.method === "GET") {
    return handleNotificationsList(request, response, urlObject);
  }

  if (pathname === "/api/notifications" && request.method === "POST") {
    return handleNotificationCreate(request, response);
  }

  if (pathname.startsWith("/api/notifications/") && pathname.endsWith("/read") && request.method === "PATCH") {
    const parts = pathname.split("/");
    return handleNotificationRead(request, response, parts[3]);
  }

  if (pathname === "/api/profile" && request.method === "GET") {
    return handleProfileGet(request, response);
  }

  if (pathname === "/api/profile" && request.method === "PATCH") {
    return handleProfileUpdate(request, response);
  }

  if (pathname === "/api/overview" && request.method === "GET") {
    return handleOverview(request, response);
  }

  return sendJson(response, 404, { error: "API route topilmadi." });
}

async function handlePages(request, response, urlObject) {
  let pathname = urlObject.pathname;

  if (pathname === "/") {
    pathname = "/index.html";
  }

  if (pathname === "/dashboard") {
    const context = await getSessionContext(request);
    if (context?.user) {
      return redirect(response, mapDashboardPath(context.user.role));
    }
    return redirect(response, "/login.html");
  }

  if (pathname === "/profile") {
    return redirect(response, "/profile.html");
  }

  if (pathname === "/login.html") {
    const context = await getSessionContext(request);
    if (context?.user) {
      return redirect(response, mapDashboardPath(context.user.role));
    }
  }

  if (protectedPages[pathname]) {
    const context = await getSessionContext(request);
    if (!context || context.invalid) {
      return redirect(response, `/login.html?next=${encodeURIComponent(pathname)}`);
    }

    if (!protectedPages[pathname].includes(context.user.role)) {
      return redirect(response, mapDashboardPath(context.user.role));
    }
  }

  const target = path.normalize(path.join(PUBLIC_DIR, pathname.replace(/^\/+/, "")));
  if (!target.startsWith(PUBLIC_DIR)) {
    return sendHtml(response, 403, "<h1>403</h1><p>Ruxsat yo'q.</p>");
  }

  if (path.extname(target) === ".html") {
    return serveFile(response, target);
  }

  return sendHtml(response, 404, "<h1>404</h1><p>Sahifa topilmadi.</p>");
}

async function requestListener(request, response) {
  try {
    const urlObject = new URL(request.url, `http://${request.headers.host || `localhost:${PORT}`}`);

    if (urlObject.pathname.startsWith("/api/")) {
      return await handleApi(request, response, urlObject);
    }

    return await handlePages(request, response, urlObject);
  } catch (error) {
    console.error(error);
    const statusCode = error.message === "Body juda katta" ? 413 : 500;
    return sendJson(response, statusCode, { error: error.message || "Server xatosi." });
  }
}

async function start() {
  await loadMongoDriver();
  await connectDatabase();
  await reloadCameraMonitorService();

  const server = http.createServer(requestListener);
  server.listen(PORT, () => {
    console.log(`G'isht platforma ishga tushdi: http://localhost:${PORT}`);
    if (storageMode === "mongo") {
      console.log(`MongoDB: ${MONGODB_URI}/${DB_NAME}`);
    } else {
      console.log(`Storage: local file (${LOCAL_DB_FILE})`);
    }
  });

  const closeServer = async () => {
    try {
      await stopAllCameraMonitors();
      await mongoClient?.close();
    } finally {
      process.exit(0);
    }
  };

  process.on("SIGINT", closeServer);
  process.on("SIGTERM", closeServer);
}

start().catch((error) => {
  console.error("Server ishga tushmadi:", error);
  process.exit(1);
});
