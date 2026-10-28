#!/usr/bin/env python3
"""
SIG Super Market arbitrage bot - Midterm Elections competition
===============================================================

No forecasting and no news. The bot only takes price inconsistencies that pay
off whatever happens, using atomic all-or-none baskets (POST /orders/multi-leg
with executionMode "allOrNone"): every leg fills completely at your limit
prices, or nothing executes and nothing is left resting on the book.

What it scans for
  1. Complete sets: the outcomes of one market where exactly one can win, plus
     any mutually exclusive / complementary set the platform's relationship
     graph (ALL) reports.
         sum of best YES asks < 1   ->  buy YES on every outcome
         sum of best YES bids > 1   ->  buy NO on every outcome
  2. Logical links from the relationship graph: implication, AND / OR / NOT and
     boolean expressions. For up to 6 linked contracts the bot lists every
     basket of YES / NO buys, finds the worst payout over all outcomes the logic
     allows, and trades only if that worst payout is higher than the price paid.
Each basket is sized by walking the order book so every share keeps at least
the minimum edge, and is capped by a share of your buying power.

Setup (Windows, Python 3.8+)
  pip install requests
  Save your API key (it needs BOTH the read and the trade scope) in a file
  called api_key.txt next to this script, or set SUPERMARKET_API_KEY.
  python sig_arb_bot.py                    live; stops by itself when the competition ends
  python sig_arb_bot.py --dry-run --once   optional: shows what it finds, places nothing
  python sig_arb_bot.py --selftest         optional: offline check of the maths, no key needed

Follow strategy (optional, switched on with --follow). This is the part that can
lose money. It compares SIG prices with Polymarket / Kalshi for the same
questions (market pairs you have checked, listed in follow_map.json) and buys
the side SIG underprices when the gap is large. Stakes are a fraction of the
Kelly stake with hard caps per market and in total, and it stops itself if the
account falls too far. Arbitrage keeps running next to it.
  python sig_arb_bot.py --list-markets             write all open SIG markets to sig_markets.csv
  python sig_arb_bot.py --follow --dry-run --once  show the gaps and what it would buy
  python sig_arb_bot.py --follow                   live: arbitrage plus follow
follow_map.json looks like this (exchange = the SIG exchange id in sig_markets.csv):
  {"markets": [{"exchange": 123456, "name": "Democrats win the Senate",
                "sources": [{"venue": "polymarket", "slug": "market-slug", "outcome": "Yes"},
                            {"venue": "kalshi", "ticker": "MARKET-TICKER"}]}]}

Written next to the script: sig_arb_bot.log, sig_arb_trades.jsonl
Stop it any time with Ctrl+C. It never leaves resting orders behind.
All tunables are in the Config class below.

Known limits
  - A cancelled / N-A market is refunded at cost, which can break the guarantee
    on cross-market baskets. Rare, but possible.
  - Relationship types that cannot be modelled safely (ladders without a clear
    direction, IF) are skipped.
  - Standard accounts get 100 reads and 30 writes per minute. The bot stays
    under that.
"""
from __future__ import annotations

import argparse
import csv
import itertools
import json
import logging
import logging.handlers
import math
import os
import random
import sys
import threading
import time
import uuid
from collections import Counter, deque
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, field
from datetime import datetime, timedelta, timezone
from pathlib import Path
from typing import Any, Callable, Deque, Dict, List, Optional, Set, Tuple

try:
    import requests
except ImportError:
    sys.exit("The 'requests' package is missing. Run:  pip install requests")

# Optional: paste the key here instead of using api_key.txt / SUPERMARKET_API_KEY.
API_KEY_IN_FILE = ""

SCRIPT_DIR = Path(__file__).resolve().parent
KEY_FILE = SCRIPT_DIR / "api_key.txt"
LOG_FILE = SCRIPT_DIR / "sig_arb_bot.log"
TRADE_LOG = SCRIPT_DIR / "sig_arb_trades.jsonl"
MAP_FILE = SCRIPT_DIR / "follow_map.json"
MARKETS_CSV = SCRIPT_DIR / "sig_markets.csv"

SCALE = 200              # price ticks per 1.00 (tick size is 0.005)
BIG = 10 ** 9            # "unlimited" size for the first, price-only pass
MAX_LEGS = 10            # multi-leg order limit
MAX_GENERIC_NODES = 6    # brute-force limit for relationship groups

FATAL_CODES = {
    "MISSING_API_KEY", "INVALID_API_KEY", "API_KEY_REVOKED", "API_KEY_EXPIRED",
    "ACCOUNT_BANNED", "INSUFFICIENT_SCOPES",
}
ACTION_CODES = {"TERMS_NOT_ACKNOWLEDGED", "RESIDENCE_UPDATE_REQUIRED", "FORBIDDEN"}

HELP = {
    "INSUFFICIENT_SCOPES": "The API key is missing a scope. Create a new key with BOTH 'read' and 'trade' ticked.",
    "INVALID_API_KEY": "The key was not recognised. Check api_key.txt (no quotes or spaces) or create a new key.",
    "MISSING_API_KEY": "No API key was sent. Check api_key.txt or SUPERMARKET_API_KEY.",
    "API_KEY_REVOKED": "This key was revoked. Create a new one.",
    "API_KEY_EXPIRED": "This key has expired. Create a new one.",
    "ACCOUNT_BANNED": "The account is banned. Contact the organizers.",
    "TERMS_NOT_ACKNOWLEDGED": "Log in on the site and accept the current Terms / competition rules. "
                              "The bot keeps retrying.",
    "RESIDENCE_UPDATE_REQUIRED": "Update your country / state in your profile on the site. The bot keeps retrying.",
    "FORBIDDEN": "Access refused. Usual causes: email not confirmed, not enrolled in the competition "
                 "(join it once on the site), or trading not open yet. The bot keeps retrying.",
}

log = logging.getLogger("sigarb")


# ---------------------------------------------------------------------------
# settings
# ---------------------------------------------------------------------------

@dataclass
class Config:
    api_key: str = ""
    base_urls: List[str] = field(default_factory=lambda: [
        "https://sig.thesuper.market/api/v1",
        "https://www.thesuper.market/api/v1",
    ])
    tournament_slug: str = ""           # empty = auto-detect the Midterm competition
    tournament_hint: str = "midterm"
    cycle_seconds: float = 4.0          # pause between scans
    universe_refresh_seconds: float = 600.0
    account_refresh_seconds: float = 90.0
    min_edge_ticks: int = 1             # minimum guaranteed profit per set, in ticks (1 tick = 0.005)
    min_basket_profit: float = 1.0      # skip baskets expected to earn less than this (SUSQies)
    max_cost_fraction: float = 0.25     # one basket may use at most this share of buying power
    max_basket_cost: float = 25000.0    # ... and at most this many SUSQies
    max_sets: int = 20000               # upper bound on shares per leg
    max_plausible_edge: float = 0.30    # a per-set edge above this is treated as a modelling error
    max_candidates_per_cycle: int = 6
    depth: int = 30                     # order book levels read per side
    read_budget: int = 85               # platform cap is 100 reads per minute
    write_budget: int = 24              # platform cap is 30 writes per minute
    structural_me: bool = True          # also treat plain multi-outcome markets as complete sets
    dry_run: bool = False
    once: bool = False
    verbose: bool = False
    # follow strategy (only used with --follow)
    follow: bool = False
    follow_blend: float = 0.85                    # weight on the outside price, the rest on SIG's own mid
    follow_enter_edge: float = 0.04               # buy only if the expected profit per share is at least this
    follow_kelly: float = 0.30                    # share of the Kelly stake to use
    follow_max_per_market: float = 0.05           # most of your account value in one market
    follow_max_per_market_certain: float = 0.12   # ... when the outcome looks near-certain
    follow_certain_prob: float = 0.96
    follow_max_total: float = 0.50                # most of your account value in all followed markets together
    follow_max_drawdown: float = 0.35             # stop following if the account falls this far below its start
    follow_max_gap: float = 0.50                  # ignore bigger gaps (almost surely a mapping mistake)
    follow_min_shares: int = 10
    follow_min_volume: float = 5000.0             # thinner outside markets count for less
    follow_max_disagreement: float = 0.12         # skip if two outside sources differ by more than this
    follow_spike: float = 0.25                    # a one-read jump bigger than this needs a second reading
    follow_max_age: float = 180.0                 # ignore outside prices older than this many seconds
    follow_poll_seconds: float = 20.0
    follow_fast_poll_seconds: float = 8.0         # used in the last 20 hours before the end
    follow_positions_seconds: float = 30.0
    follow_max_orders_per_cycle: int = 3


# ---------------------------------------------------------------------------
# small helpers
# ---------------------------------------------------------------------------

def to_ticks(price: Any) -> Optional[int]:
    """0.545 -> 109. Returns None for missing or untradeable prices."""
    try:
        t = int(round(float(price) * SCALE))
    except (TypeError, ValueError):
        return None
    return t if 0 < t < SCALE else None


def ticks_to_price(t: int) -> float:
    return round(t / SCALE, 3)


def parse_dt(value: Optional[str]) -> Optional[datetime]:
    if not value:
        return None
    try:
        dt = datetime.fromisoformat(str(value).replace("Z", "+00:00"))
    except ValueError:
        return None
    return dt if dt.tzinfo else dt.replace(tzinfo=timezone.utc)


class StopBot(Exception):
    def __init__(self, message: str, code: int = 0):
        super().__init__(message)
        self.code = code


class ApiError(Exception):
    def __init__(self, status: int, code: str, message: str,
                 details: Optional[dict] = None, retry_after: Optional[float] = None):
        super().__init__(f"{status} {code}: {message}")
        self.status = status
        self.code = code
        self.message = message
        self.details = details or {}
        self.retry_after = retry_after


def classify(e: ApiError) -> str:
    """fatal = stop; wait = the user has to fix something on the site, keep retrying; retry = transient."""
    if e.code in FATAL_CODES:
        return "fatal"
    if e.code in ACTION_CODES or e.status == 403:
        return "wait"
    return "retry"


def explain(e: ApiError) -> str:
    text = f"{e.code}: {e.message}"
    if e.code in HELP:
        text += "\n    -> " + HELP[e.code]
    return text


# ---------------------------------------------------------------------------
# data model
# ---------------------------------------------------------------------------

@dataclass
class Book:
    bids: List[Tuple[int, int]] = field(default_factory=list)   # (price ticks, size), best (highest) first
    asks: List[Tuple[int, int]] = field(default_factory=list)   # (price ticks, size), best (lowest) first


@dataclass
class Combo:
    signs: Tuple[int, ...]   # per exchange: +1 buy YES, -1 buy NO, 0 not used
    floor: int               # guaranteed payout in whole shares over every outcome the logic allows


@dataclass
class Group:
    gid: str
    label: str
    exch: List[int]
    combos: List[Combo]
    market_id: Optional[str] = None   # set when exch is exactly one market's exchange list
    source: str = ""


@dataclass
class Plan:
    group: Group
    legs: List[Tuple[int, int]]       # (exchange id, sign)
    limits: List[int]                 # limit price per leg in ticks, of the share being bought
    qty: int
    cost_ticks: int
    profit_ticks: int
    floor: int

    @property
    def cost(self) -> float:
        return self.cost_ticks / SCALE

    @property
    def profit(self) -> float:
        return self.profit_ticks / SCALE

    @property
    def worst_profit(self) -> float:
        """Profit if every leg fills at its limit price (the worst case)."""
        return self.qty * (self.floor * SCALE - sum(self.limits)) / SCALE


def parse_levels(raw: Any) -> List[Tuple[int, int]]:
    out: List[Tuple[int, int]] = []
    for lv in raw or []:
        try:
            price = to_ticks(lv["price"])
            size = int(float(lv["quantity"]))
        except (KeyError, TypeError, ValueError):
            continue
        if price is not None and size > 0:
            out.append((price, size))
    return out


def make_book(bids_raw: Any, asks_raw: Any) -> Book:
    return Book(sorted(parse_levels(bids_raw), key=lambda x: -x[0]),
                sorted(parse_levels(asks_raw), key=lambda x: x[0]))


# ---------------------------------------------------------------------------
# pricing maths
# ---------------------------------------------------------------------------

def levels_for(book: Book, sign: int) -> List[Tuple[int, int]]:
    """What we would pay and how much is available, cheapest first.
    sign +1: buy YES at the asks. sign -1: buy NO, which hits the YES bids at 1 - bid."""
    if sign > 0:
        return list(book.asks)
    return [(SCALE - price, size) for price, size in book.bids]


def size_levels(levels: List[List[Tuple[int, int]]], floor_ticks: int, min_edge: int,
                max_sets: int, max_cost_ticks: int) -> Optional[Tuple[int, List[int], int, int]]:
    """Walk the books of all legs together. Keep adding sets while the next set still
    earns at least min_edge ticks. Returns (qty, limit price per leg, cost, profit) in ticks."""
    n = len(levels)
    if n == 0 or any(not lv for lv in levels):
        return None
    idx = [0] * n
    rem = [lv[0][1] for lv in levels]
    limits = [lv[0][0] for lv in levels]
    qty = cost = profit = 0
    while qty < max_sets:
        prices = [levels[i][idx[i]][0] for i in range(n)]
        unit = sum(prices)
        edge = floor_ticks - unit
        if edge < min_edge:
            break
        step = min(min(rem), max_sets - qty)
        step = min(step, (max_cost_ticks - cost) // unit)
        if step <= 0:
            break
        qty += step
        cost += step * unit
        profit += step * edge
        limits = prices
        exhausted = False
        for i in range(n):
            rem[i] -= step
            if rem[i] <= 0:
                idx[i] += 1
                if idx[i] >= len(levels[i]):
                    exhausted = True
                else:
                    rem[i] = levels[i][idx[i]][1]
        if exhausted:
            break
    if qty <= 0:
        return None
    return qty, limits, cost, profit


def plan_combo(group: Group, combo: Combo, books: Dict[int, Book], min_edge: int,
               max_sets: int, max_cost_ticks: int) -> Optional[Plan]:
    legs: List[Tuple[int, int]] = []
    levels: List[List[Tuple[int, int]]] = []
    for eid, sign in zip(group.exch, combo.signs):
        if sign == 0:
            continue
        book = books.get(eid)
        if book is None:
            return None
        lv = levels_for(book, sign)
        if not lv:
            return None
        legs.append((eid, sign))
        levels.append(lv)
    if not legs or len(legs) > MAX_LEGS:
        return None
    res = size_levels(levels, combo.floor * SCALE, min_edge, max_sets, max_cost_ticks)
    if res is None:
        return None
    qty, limits, cost, profit = res
    return Plan(group, legs, limits, qty, cost, profit, combo.floor)


def best_plan(group: Group, books: Dict[int, Book], min_edge: int, max_sets: int,
              max_cost_ticks: int) -> Optional[Plan]:
    best: Optional[Plan] = None
    for combo in group.combos:
        plan = plan_combo(group, combo, books, min_edge, max_sets, max_cost_ticks)
        if plan is not None and (best is None or plan.profit_ticks > best.profit_ticks):
            best = plan
    return best


# ---------------------------------------------------------------------------
# logic: which baskets pay off in every possible outcome
# ---------------------------------------------------------------------------

def me_combos(n: int, exhaustive: bool) -> List[Combo]:
    """n outcomes of which exactly one (exhaustive) or at most one (not exhaustive) pays 1."""
    combos = [Combo(tuple([-1] * n), n - 1)]         # NO on all: pays at least n - 1
    if exhaustive:
        combos.append(Combo(tuple([1] * n), 1))      # YES on all: pays exactly 1
    return combos


def collect_leaves(node: Any) -> Optional[Set[int]]:
    """Exchange ids used by a boolean expression, or None if it uses something we cannot model (IF)."""
    if not isinstance(node, dict):
        return None
    kind = node.get("kind")
    if kind == "leaf":
        return {int(node["exchangeId"])}
    if kind in ("and", "or"):
        found: Set[int] = set()
        for child in node.get("children") or []:
            sub = collect_leaves(child)
            if sub is None:
                return None
            found |= sub
        return found or None
    if kind == "not":
        return collect_leaves(node.get("child"))
    return None


def eval_expr(node: dict, s: Dict[int, int]) -> bool:
    kind = node["kind"]
    if kind == "leaf":
        return bool(s[int(node["exchangeId"])])
    if kind == "and":
        return all(eval_expr(c, s) for c in node["children"])
    if kind == "or":
        return any(eval_expr(c, s) for c in node["children"])
    return not eval_expr(node["child"], s)          # "not"


def build_predicate(rel: dict, ids: List[int]) -> Optional[Callable[[Dict[int, int]], bool]]:
    """Turn a relationship into a test: is this YES/NO combination of the contracts possible?"""
    rtype = str(rel.get("type"))
    roles = {int(n["exchangeId"]): n.get("role") for n in rel.get("nodes") or []}

    def by_role(role: str) -> List[int]:
        return [i for i in ids if roles.get(i) == role]

    if rtype in ("implication", "monotonic"):
        ante, cons = by_role("antecedent"), by_role("consequent")
        if not (len(ante) == 1 and len(cons) == 1):
            d = rel.get("direction") or {}
            if d.get("kind") == "antecedent_to_consequent":
                ante = [int(x) for x in d.get("fromExchangeIds") or []]
                cons = [int(x) for x in d.get("toExchangeIds") or []]
        if (len(ids) == 2 and len(ante) == 1 and len(cons) == 1 and ante[0] != cons[0]
                and ante[0] in ids and cons[0] in ids):
            a0, c0 = ante[0], cons[0]
            return lambda s: not (s[a0] and not s[c0])
        return None

    if rtype in ("boolean_and", "boolean_or", "boolean_not", "boolean_expression"):
        out, inp = by_role("output"), by_role("input")
        if len(out) != 1 or not inp or len(out) + len(inp) != len(ids):
            return None
        o = out[0]
        if rtype == "boolean_and":
            return lambda s: bool(s[o]) == all(s[i] for i in inp)
        if rtype == "boolean_or":
            return lambda s: bool(s[o]) == any(s[i] for i in inp)
        if rtype == "boolean_not":
            if len(inp) != 1:
                return None
            i0 = inp[0]
            return lambda s: bool(s[o]) != bool(s[i0])
        expr = rel.get("expression")
        leaves = collect_leaves(expr) if isinstance(expr, dict) else None
        if not leaves or not leaves <= set(inp):
            return None
        return lambda s: bool(s[o]) == eval_expr(expr, s)

    return None


def combos_from_predicate(ids: List[int], pred: Callable[[Dict[int, int]], bool]) -> List[Combo]:
    """Enumerate the possible outcomes, then every basket of YES (+1) / NO (-1) / none (0) buys.
    Keep baskets whose worst-case payout is at least 1 share and that have no useless leg."""
    n = len(ids)
    states = [bits for bits in itertools.product((0, 1), repeat=n) if pred(dict(zip(ids, bits)))]
    if not states:
        return []
    floors: Dict[Tuple[int, ...], int] = {}
    for c in itertools.product((-1, 0, 1), repeat=n):
        worst: Optional[int] = None
        for s in states:
            pay = 0
            for ci, si in zip(c, s):
                if ci == 1:
                    pay += si
                elif ci == -1:
                    pay += 1 - si
            if worst is None or pay < worst:
                worst = pay
        floors[c] = worst if worst is not None else 0
    combos: List[Combo] = []
    for c, f in floors.items():
        if f < 1:
            continue
        useful = True
        for i, ci in enumerate(c):
            if ci != 0 and floors[c[:i] + (0,) + c[i + 1:]] >= f:
                useful = False        # dropping this leg keeps the payout and saves its cost
                break
        if useful:
            combos.append(Combo(c, f))
    return combos


# ---------------------------------------------------------------------------
# API layer
# ---------------------------------------------------------------------------

class RateLimiter:
    """Sliding 60 second window."""

    def __init__(self, per_minute: int):
        self.per_minute = max(1, per_minute)
        self.stamps: Deque[float] = deque()

    def _trim(self, now: float) -> None:
        while self.stamps and now - self.stamps[0] >= 60.0:
            self.stamps.popleft()

    def wait_time(self) -> float:
        now = time.monotonic()
        self._trim(now)
        if len(self.stamps) < self.per_minute:
            return 0.0
        return 60.0 - (now - self.stamps[0]) + 0.05

    def acquire(self, max_wait: Optional[float] = None) -> bool:
        wait = self.wait_time()
        if max_wait is not None and wait > max_wait:
            return False
        if wait > 0:
            time.sleep(wait)
        now = time.monotonic()
        self._trim(now)
        self.stamps.append(now)
        return True


class Api:
    def __init__(self, cfg: Config):
        self.cfg = cfg
        self.base = cfg.base_urls[0]
        self.session = requests.Session()
        self.session.headers.update({
            "Authorization": f"Bearer {cfg.api_key}",
            "Accept": "application/json",
            "User-Agent": "sig-arb-bot/1.0",
        })
        self.reads = RateLimiter(cfg.read_budget)
        self.writes = RateLimiter(cfg.write_budget)

    @staticmethod
    def _error(r: requests.Response) -> ApiError:
        code, message, details = f"HTTP_{r.status_code}", r.text[:300], {}
        try:
            body = r.json()
            err = body.get("error") if isinstance(body, dict) else None
            if isinstance(err, dict):
                code = str(err.get("code") or code)
                message = str(err.get("message") or message)
                details = err.get("details") or {}
            elif isinstance(err, str):
                message = err
        except ValueError:
            pass
        retry_after: Optional[float] = None
        raw = r.headers.get("Retry-After")
        if raw:
            try:
                retry_after = float(raw)
            except ValueError:
                retry_after = None
        return ApiError(r.status_code, code, message,
                        details if isinstance(details, dict) else {}, retry_after)

    def request(self, method: str, path: str, params: Optional[dict] = None, body: Optional[dict] = None,
                write: bool = False, retry_429: bool = True, max_attempts: int = 4,
                max_wait: Optional[float] = None) -> Any:
        limiter = self.writes if write else self.reads
        url = self.base + path
        last: Optional[ApiError] = None
        for attempt in range(1, max_attempts + 1):
            if not limiter.acquire(max_wait):
                raise ApiError(0, "LOCAL_RATE_LIMIT", "local request budget used up for now")
            try:
                r = self.session.request(method, url, params=params, json=body, timeout=(5, 20))
            except requests.RequestException as exc:
                last = ApiError(0, "NETWORK", f"{type(exc).__name__}: {exc}")
                if attempt < max_attempts:
                    time.sleep(min(2 ** attempt, 15) + random.random())
                continue
            if r.status_code < 400:
                if not r.content:
                    return {}
                try:
                    return r.json()
                except ValueError:
                    raise ApiError(r.status_code, "BAD_JSON", r.text[:200])
            err = self._error(r)
            last = err
            transient = err.status in (502, 503) or err.code in ("TX_CONFLICT", "SERVICE_UNAVAILABLE")
            if err.status == 429 and retry_429:
                transient = True
            if not transient or attempt == max_attempts:
                raise err
            delay = err.retry_after if err.retry_after is not None else min(2 ** attempt, 20)
            delay = min(delay, 65.0) + random.random()
            log.debug("%s %s -> %s, retrying in %.1fs", method, path, err.code, delay)
            time.sleep(delay)
        assert last is not None
        raise last

    def connect(self) -> dict:
        """Find the host that accepts the key and return the account."""
        last: Optional[ApiError] = None
        for base in self.cfg.base_urls:
            self.base = base
            try:
                return self.request("GET", "/account", max_attempts=2)
            except ApiError as e:
                last = e
                log.info("%s did not work: %s", base, e)
        assert last is not None
        raise last


# ---------------------------------------------------------------------------
# follow strategy: trade SIG toward prices on deeper real-money markets
# ---------------------------------------------------------------------------

@dataclass
class ExtQuote:
    prob: float                  # chance that the mapped outcome happens
    spread: Optional[float]      # bid/ask spread at the source, None if unknown
    volume: float                # traded volume the source reports
    venue: str


def to_float(value: Any) -> Optional[float]:
    try:
        return float(value)
    except (TypeError, ValueError):
        return None


def as_list(value: Any) -> list:
    """Polymarket sends some lists as JSON text."""
    if isinstance(value, str):
        try:
            value = json.loads(value)
        except ValueError:
            return []
    return value if isinstance(value, list) else []


def mid_of(bid: Optional[int], ask: Optional[int]) -> Optional[float]:
    if bid is not None and ask is not None:
        return (bid + ask) / 2.0 / SCALE
    if bid is not None:
        return bid / SCALE
    if ask is not None:
        return ask / SCALE
    return None


def tick_str(t: Optional[int]) -> str:
    return f"{t / SCALE:.3f}" if t else "-"


class ExternalPrices:
    """Public prices from Polymarket and Kalshi. Has its own session, so the SIG key is never sent there."""

    POLY = "https://gamma-api.polymarket.com/markets"
    KALSHI = "https://api.elections.kalshi.com/trade-api/v2/markets/"

    def __init__(self) -> None:
        self.session = requests.Session()
        self.session.headers.update({"Accept": "application/json", "User-Agent": "Mozilla/5.0 (sig-arb-bot)"})

    def _get(self, url: str, params: Optional[dict] = None) -> Any:
        try:
            r = self.session.get(url, params=params, timeout=(5, 15))
        except requests.RequestException as exc:
            log.debug("outside price request failed: %s", exc)
            return None
        if r.status_code != 200:
            log.debug("outside price request %s -> HTTP %s", url, r.status_code)
            return None
        try:
            return r.json()
        except ValueError:
            return None

    def polymarket(self, slug: str, outcome: str = "Yes") -> Optional[ExtQuote]:
        data = self._get(self.POLY, {"slug": slug})
        if isinstance(data, dict):
            data = data.get("data") or data.get("markets")
        if not isinstance(data, list) or not data or not isinstance(data[0], dict):
            return None
        m = data[0]
        if m.get("closed") or m.get("active") is False:
            return None
        names = [str(x).strip().lower() for x in as_list(m.get("outcomes"))]
        prices = [to_float(x) for x in as_list(m.get("outcomePrices"))]
        want = outcome.strip().lower()
        if want not in names:
            return None
        idx = names.index(want)
        if idx >= len(prices) or prices[idx] is None:
            return None
        bid, ask = to_float(m.get("bestBid")), to_float(m.get("bestAsk"))
        spread = ask - bid if bid is not None and ask is not None and ask >= bid else None
        volume = to_float(m.get("volume")) or to_float(m.get("volumeNum")) or 0.0
        return ExtQuote(float(prices[idx]), spread, volume, "polymarket")

    def kalshi(self, ticker: str) -> Optional[ExtQuote]:
        data = self._get(self.KALSHI + ticker)
        m = data.get("market") if isinstance(data, dict) else None
        if not isinstance(m, dict) or str(m.get("status")) not in ("active", "open"):
            return None

        def price(name: str) -> Optional[float]:
            v = to_float(m.get(name + "_dollars"))
            if v is None:
                cents = to_float(m.get(name))
                v = cents / 100.0 if cents is not None else None
            return v

        bid, ask, last = price("yes_bid"), price("yes_ask"), price("last_price")
        if bid is not None and ask is not None and bid > 0 and ask >= bid:
            prob, spread = (bid + ask) / 2.0, ask - bid
        elif last is not None:
            prob, spread = last, None
        else:
            return None
        volume = to_float(m.get("volume_fp")) or to_float(m.get("volume")) or 0.0
        return ExtQuote(prob, spread, volume, "kalshi")


def combine_quotes(quotes: List[ExtQuote], min_volume: float, max_disagreement: float) -> Optional[float]:
    """Weighted mean of the outside probabilities, or None if they are too thin or disagree."""
    weighted: List[Tuple[float, float]] = []
    for q in quotes:
        if not 0.0 < q.prob < 1.0:
            continue
        if q.spread is None or q.spread > 0.15:
            weight = 0.25
        elif q.spread > 0.08:
            weight = 0.5
        else:
            weight = 1.0
        if q.volume < min_volume:
            weight *= 0.5
        weighted.append((q.prob, weight))
    if not weighted:
        return None
    probs = [p for p, _ in weighted]
    if len(probs) > 1 and max(probs) - min(probs) > max_disagreement:
        return None
    total = sum(w for _, w in weighted)
    if total < 0.4:
        return None
    return sum(p * w for p, w in weighted) / total


@dataclass
class Intent:
    side: str          # "yes" or "no"
    fair: float        # our estimate of the chance that YES happens
    edge: float        # expected profit per share at the current best price
    max_price: int     # highest price we accept for the share we buy, in ticks
    shares: int        # shares to buy (includes closing any opposite position)


def follow_intent(p_ext: float, bid: Optional[int], ask: Optional[int], cfg: Config, equity: float,
                  net_qty: float, scale: float = 1.0) -> Optional[Intent]:
    """Buy YES or NO when SIG is cheap against the outside price. net_qty = shares held (+YES / -NO)."""
    mid = mid_of(bid, ask)
    if mid is None or equity <= 0:
        return None
    if abs(p_ext - mid) > cfg.follow_max_gap:
        return None                       # far more likely a mapping mistake than a real gap
    fair = cfg.follow_blend * p_ext + (1.0 - cfg.follow_blend) * mid
    edge_yes = fair - ask / SCALE if ask is not None else -1.0
    edge_no = bid / SCALE - fair if bid is not None else -1.0
    if ask is not None and (bid is None or edge_yes >= edge_no):
        side, edge, price, win = "yes", edge_yes, ask / SCALE, fair
    elif bid is not None:
        side, edge, price, win = "no", edge_no, 1.0 - bid / SCALE, 1.0 - fair
    else:
        return None
    if edge < cfg.follow_enter_edge or not 0.0 < price < 1.0:
        return None
    kelly = (win - price) / (1.0 - price)             # share of the account to stake at full Kelly
    cap = cfg.follow_max_per_market_certain if win >= cfg.follow_certain_prob else cfg.follow_max_per_market
    stake_frac = min(cfg.follow_kelly * kelly, cap) * scale
    if stake_frac <= 0:
        return None
    target = int(stake_frac * equity / price)         # shares we want on this side in total
    if side == "yes":
        held_same, held_opp = max(0.0, net_qty), max(0.0, -net_qty)
    else:
        held_same, held_opp = max(0.0, -net_qty), max(0.0, net_qty)
    shares = int(target - held_same + held_opp)
    if shares < cfg.follow_min_shares:
        return None
    max_price = int((win - 0.5 * cfg.follow_enter_edge) * SCALE)
    if max_price < 1:
        return None
    return Intent(side, fair, edge, max_price, shares)


def follow_fill(book: Book, intent: Intent) -> Optional[Tuple[int, int, float]]:
    """Walk the book for what we can buy at or below the price we accept: (shares, worst price in ticks, cost)."""
    levels = levels_for(book, 1 if intent.side == "yes" else -1)
    qty = 0
    cost = 0.0
    limit = 0
    for price, size in levels:
        if price > intent.max_price or qty >= intent.shares:
            break
        take = min(size, intent.shares - qty)
        qty += take
        cost += take * price / SCALE
        limit = price
    if qty <= 0:
        return None
    return qty, limit, cost


class Follower:
    """Trades SIG toward Polymarket / Kalshi prices for the market pairs listed in follow_map.json."""

    def __init__(self, bot: "Bot"):
        self.bot = bot
        self.cfg = bot.cfg
        self.ext = ExternalPrices()
        self.pool = ThreadPoolExecutor(max_workers=4)
        self.entries: List[dict] = []
        self.loaded = False
        self.started = False
        self.active = True
        self.errors = 0
        self.ext_p: Dict[int, Tuple[float, float]] = {}        # exchange id -> (probability, time read)
        self.pending: Dict[int, float] = {}
        self.fail_streak = 0
        self.positions: Dict[int, Tuple[float, float]] = {}    # exchange id -> (shares, +YES / -NO; cost basis)
        self.positions_ok = False
        self.pos_value = 0.0
        self.equity = 0.0
        self.equity_ok = False
        self.baseline = 0.0
        self.cool: Dict[int, float] = {}
        self.last_positions = 0.0
        self.last_report = 0.0
        self.stats: Counter = Counter()

    # -- mapping -----------------------------------------------------------

    def load_map(self) -> None:
        self.loaded = True
        if not MAP_FILE.exists():
            log.warning("follow strategy is on, but %s does not exist yet. Run with --list-markets, "
                        "send me sig_markets.csv and I will build it.", MAP_FILE.name)
            self.active = False
            return
        try:
            raw = json.loads(MAP_FILE.read_text(encoding="utf-8-sig"))
        except (OSError, ValueError) as exc:
            log.error("could not read %s: %s", MAP_FILE.name, exc)
            self.active = False
            return
        items = raw.get("markets") if isinstance(raw, dict) else raw
        entries: List[dict] = []
        for item in (items if isinstance(items, list) else []):
            if not isinstance(item, dict) or item.get("enabled", True) is False:
                continue
            try:
                eid = int(item["exchange"])
            except (KeyError, TypeError, ValueError):
                continue
            sources = [s for s in item.get("sources") or [] if isinstance(s, dict)]
            scale = to_float(item.get("scale", 1.0))
            if not sources or scale is None or scale <= 0:
                continue
            entries.append({"exchange": eid, "name": str(item.get("name") or eid),
                            "sources": sources, "scale": scale})
        self.entries = entries
        log.info("follow strategy: %d mapped markets read from %s", len(entries), MAP_FILE.name)
        if not entries:
            self.active = False

    def exchange_ids(self) -> Set[int]:
        if not self.loaded:
            self.load_map()
        return {e["exchange"] for e in self.entries} if self.active else set()

    # -- outside prices ----------------------------------------------------

    def poll_seconds(self) -> float:
        end = self.bot.t_end
        if end is not None and (end - datetime.now(timezone.utc)).total_seconds() < 20 * 3600:
            return self.cfg.follow_fast_poll_seconds
        return self.cfg.follow_poll_seconds

    @staticmethod
    def source_key(s: dict) -> Tuple[str, str, str]:
        return (str(s.get("venue", "")).lower(), str(s.get("slug") or s.get("ticker") or ""),
                str(s.get("outcome", "Yes")).lower())

    def fetch_source(self, s: dict) -> Optional[ExtQuote]:
        venue = str(s.get("venue", "")).lower()
        try:
            if venue == "polymarket" and s.get("slug"):
                return self.ext.polymarket(str(s["slug"]).strip(), str(s.get("outcome", "Yes")))
            if venue == "kalshi" and s.get("ticker"):
                return self.ext.kalshi(str(s["ticker"]).strip())
        except Exception:
            log.debug("outside source failed: %s", s, exc_info=True)
        return None

    def refresh_external(self) -> None:
        keys: Dict[Tuple[str, str, str], dict] = {}
        for e in self.entries:
            for s in e["sources"]:
                keys.setdefault(self.source_key(s), s)
        fetched = dict(zip(keys.keys(), self.pool.map(self.fetch_source, list(keys.values()))))
        if keys and not any(q is not None for q in fetched.values()):
            self.fail_streak += 1
            if self.fail_streak in (1, 15):
                log.warning("follow: could not read any outside price (offline, blocked, or wrong slugs / tickers)")
        else:
            self.fail_streak = 0
        now = time.time()
        for e in self.entries:
            quotes = [q for q in (fetched.get(self.source_key(s)) for s in e["sources"]) if q is not None]
            p = combine_quotes(quotes, self.cfg.follow_min_volume, self.cfg.follow_max_disagreement)
            if p is None:
                continue
            eid = e["exchange"]
            old = self.ext_p.get(eid)
            if old is not None and now - old[1] < 600 and abs(p - old[0]) > self.cfg.follow_spike:
                prev = self.pending.get(eid)
                if prev is None or abs(prev - p) > 0.05:
                    self.pending[eid] = p          # a big one-read jump: wait for a second reading that agrees
                    continue
            self.pending.pop(eid, None)
            self.ext_p[eid] = (p, now)

    def _loop(self) -> None:
        while True:
            time.sleep(max(2.0, self.poll_seconds()))
            if not self.active:
                continue
            try:
                self.refresh_external()
            except Exception:
                log.debug("outside price refresh failed", exc_info=True)

    # -- account -----------------------------------------------------------

    def refresh_positions(self) -> None:
        bot = self.bot
        self.last_positions = time.time()
        path = f"/tournaments/{bot.t_slug}/portfolio/positions" if bot.t_slug else "/portfolio/positions"
        try:
            j = bot.api.request("GET", path)
        except ApiError as e:
            if classify(e) == "fatal":
                raise
            if e.status == 403:                    # not enrolled yet, so nothing is held
                self.positions, self.pos_value, self.positions_ok = {}, 0.0, True
                return
            self.positions_ok = False
            if e.status == 409:
                log.warning("follow: positions cannot be valued yet (a holding has no price), pausing follow orders")
            else:
                log.debug("follow: positions read failed: %s", e)
            return
        pos: Dict[int, Tuple[float, float]] = {}
        total_value = 0.0
        for row in j.get("positions") or []:
            try:
                eid = int(row["exchangeId"])
            except (KeyError, TypeError, ValueError):
                continue
            if row.get("settled"):
                continue
            pos[eid] = (to_float(row.get("quantity")) or 0.0, to_float(row.get("costBasis")) or 0.0)
            total_value += abs(to_float(row.get("marketValue")) or 0.0)
        self.positions = pos
        self.pos_value = total_value
        self.positions_ok = True

    def refresh_equity(self) -> None:
        bot = self.bot
        path = f"/tournaments/{bot.t_slug}/portfolio/pnl" if bot.t_slug else "/portfolio/pnl"
        value: Optional[float] = None
        try:
            j = bot.api.request("GET", path, params={"period": "all"})
            value = to_float(j.get("totalAccountValue"))
        except ApiError as e:
            if classify(e) == "fatal":
                raise
        self.equity_ok = value is not None and value > 0
        if value is not None and self.equity_ok:
            self.equity = value

    def check_drawdown(self) -> None:
        if not self.equity_ok:
            return
        if self.baseline <= 0:
            self.baseline = self.bot.t_initial if self.bot.t_initial > 0 else self.equity
        floor = self.baseline * (1.0 - self.cfg.follow_max_drawdown)
        if self.equity < floor:
            log.error("follow strategy stopped: account value %.0f fell below %.0f (%.0f%% under the %.0f start). "
                      "Arbitrage keeps running.", self.equity, floor, self.cfg.follow_max_drawdown * 100,
                      self.baseline)
            self.active = False

    # -- reporting ---------------------------------------------------------

    def report(self, quotes: Dict[int, Tuple[Optional[int], Optional[int]]]) -> None:
        rows: List[Tuple[float, str, float, Optional[int], Optional[int]]] = []
        for e in self.entries:
            info = self.ext_p.get(e["exchange"])
            quote = quotes.get(e["exchange"])
            if info is None or quote is None:
                continue
            mid = mid_of(quote[0], quote[1])
            if mid is None:
                continue
            rows.append((info[0] - mid, str(e["name"]), info[0], quote[0], quote[1]))
        rows.sort(key=lambda r: -abs(r[0]))
        exposure = sum(self.positions.get(e["exchange"], (0.0, 0.0))[1] for e in self.entries)
        log.info("follow: %d mapped | %d with outside prices and SIG quotes | orders %d | exposure %.0f",
                 len(self.entries), len(rows), self.stats["orders"], exposure)
        for gap, name, p, bid, ask in rows[:8]:
            log.info("  %-44s outside %.3f | SIG %s / %s | gap %+.3f", name[:44], p, tick_str(bid), tick_str(ask), gap)

    # -- trading -----------------------------------------------------------

    def step(self, quotes: Dict[int, Tuple[Optional[int], Optional[int]]]) -> None:
        if not self.loaded:
            self.load_map()
        if not self.active or not self.entries:
            return
        bot = self.bot
        if not self.started:
            self.started = True
            self.refresh_external()                  # the first read happens in the foreground
            threading.Thread(target=self._loop, name="outside-prices", daemon=True).start()
        now = time.time()
        if now - self.last_report >= 300:
            self.last_report = now
            self.report(quotes)
        if now - self.last_positions >= self.cfg.follow_positions_seconds:
            self.refresh_positions()
            if self.positions_ok:
                self.refresh_equity()
                self.check_drawdown()
        if not self.active or not self.positions_ok:
            return
        equity = self.equity if self.equity_ok else bot.balance + self.pos_value
        total_cost = sum(self.positions.get(e["exchange"], (0.0, 0.0))[1] for e in self.entries)
        orders = 0
        for e in self.entries:
            if orders >= self.cfg.follow_max_orders_per_cycle:
                break
            eid = e["exchange"]
            info = self.ext_p.get(eid)
            quote = quotes.get(eid)
            if info is None or quote is None or eid not in bot.labels:
                continue
            now = time.time()
            if now - info[1] > self.cfg.follow_max_age or self.cool.get(eid, 0.0) > now:
                continue
            net_qty = self.positions.get(eid, (0.0, 0.0))[0]
            intent = follow_intent(info[0], quote[0], quote[1], self.cfg, equity, net_qty, e["scale"])
            if intent is None:
                continue
            spent = self.trade(e, intent, equity, total_cost)
            if spent > 0:
                orders += 1
                total_cost += spent

    def trade(self, e: dict, intent: Intent, equity: float, total_cost: float) -> float:
        """Place one follow order. Returns the amount spent (0 if nothing was bought)."""
        bot = self.bot
        eid = e["exchange"]
        name = str(e["name"])
        self.cool[eid] = time.time() + 20
        try:
            book = bot.fetch_books(Group(f"F:{eid}", name, [eid], [])).get(eid)
        except ApiError as err:
            if classify(err) != "retry":
                raise
            return 0.0
        fill = follow_fill(book, intent) if book is not None else None
        if fill is None:
            log.debug("follow: nothing to buy in %s at an acceptable price", name[:50])
            return 0.0
        qty, limit, cost = fill
        room = min(self.cfg.follow_max_total * equity - total_cost, bot.buying_power * 0.95)
        if room <= 0:
            return 0.0
        if cost > room:
            qty = int(qty * room / cost)
            cost = room
        if qty < self.cfg.follow_min_shares:
            return 0.0
        price = ticks_to_price(limit)
        win = intent.fair if intent.side == "yes" else 1.0 - intent.fair
        summary = (f"{intent.side.upper()} {name[:50]} | qty {qty} up to {price:.3f} | "
                   f"chance {win:.3f}, edge {intent.edge:+.3f} | cost about {cost:.0f}")
        if self.cfg.dry_run:
            log.info("DRY RUN, would follow: %s", summary)
            self.stats["dry_run"] += 1
            return 0.0

        log.info("FOLLOW: %s", summary)
        bot.seq += 1
        leg = {"exchangeId": str(eid), "side": intent.side, "action": "buy",
               "quantity": int(qty), "price": price}
        if bot.tid:
            leg["tournamentId"] = bot.tid
        body = {"idempotencyKey": f"sigfollow-{bot.run_id}-{bot.seq}-{uuid.uuid4().hex[:8]}",
                "executionMode": "allOrNone", "legs": [leg]}
        try:
            resp = bot.api.request("POST", "/orders/multi-leg", body=body, write=True,
                                   retry_429=False, max_attempts=3, max_wait=3.0)
        except ApiError as err:
            self.on_error(err, name)
            return 0.0
        results = resp.get("results") or []
        data = ((results[0] if results else None) or {}).get("data") or {}
        got = to_float(data.get("quantityTraded")) or 0.0
        paid = to_float(data.get("totalCost")) or 0.0
        complete = got + 1e-9 >= qty
        bot.record({"kind": "follow", "exchange": eid, "name": name, "side": intent.side, "qty": qty,
                    "limit": price, "got": got, "cost": round(paid, 4), "fair": round(intent.fair, 4),
                    "edge": round(intent.edge, 4), "complete": complete})
        self.last_positions = 0.0                   # re-read positions before the next order
        bot.refresh_account_safe()
        if not complete:
            log.warning("follow order only partly filled (%.0f of %d) - check your positions on the site", got, qty)
            self.stats["partial"] += 1
            return paid
        self.stats["orders"] += 1
        log.info("FOLLOW FILLED: %.0f shares, cost %.2f", got, paid)
        return paid

    def on_error(self, err: ApiError, name: str) -> None:
        if classify(err) in ("fatal", "wait"):
            raise err
        if err.status == 400 and "executionMode" in err.details:
            log.error("this competition does not accept all-or-none orders - follow strategy switched off")
            self.active = False
        elif err.status == 400 and err.details.get("rejectionReasonCode") == "AllOrNoneNotFilled":
            log.info("follow order missed (liquidity moved): %s", name[:60])
            self.stats["misses"] += 1
        elif err.code == "LOCAL_RATE_LIMIT" or err.status == 429:
            log.info("follow order not sent (rate limit)")
        else:
            log.warning("follow order rejected for %s: %s", name[:50], err)
            self.stats["rejected"] += 1
            self.bot.refresh_account_safe()


# ---------------------------------------------------------------------------
# the bot
# ---------------------------------------------------------------------------

class Bot:
    def __init__(self, cfg: Config):
        self.cfg = cfg
        self.api = Api(cfg)
        self.tid: Optional[str] = None
        self.t_slug = ""
        self.t_initial = 0.0
        self.t_name = ""
        self.t_end: Optional[datetime] = None
        self.groups: Dict[str, Group] = {}
        self.labels: Dict[int, str] = {}
        self.watch: List[int] = []
        self.cooldown: Dict[str, float] = {}
        self.warned: Dict[str, float] = {}
        self.root_cache: Dict[str, Optional[dict]] = {}
        self.combo_cache: Dict[Tuple[Any, ...], List[Combo]] = {}
        self.near: List[Tuple[int, str]] = []
        self.quoted = 0
        self.balance = 0.0
        self.buying_power = 0.0
        self.last_universe = 0.0
        self.last_account = 0.0
        self.last_heartbeat = time.time()
        self.cycle_seconds = cfg.cycle_seconds
        self.errors = 0
        self.bad_fills = 0
        self.seq = 0
        self.run_id = uuid.uuid4().hex[:8]
        self.stats: Counter = Counter()
        self.locked_profit = 0.0
        self.listed = False
        self.ready = False
        self.follower: Optional[Follower] = Follower(self) if cfg.follow else None

    # -- small helpers -----------------------------------------------------

    def p(self, extra: Optional[dict] = None) -> dict:
        params = dict(extra or {})
        if self.tid:
            params["tournamentId"] = self.tid
        return params

    def label(self, eid: int) -> str:
        return self.labels.get(eid, str(eid))

    def sleep(self, seconds: float) -> None:
        end = time.time() + max(0.0, seconds)
        while True:
            left = end - time.time()
            if left <= 0:
                return
            time.sleep(min(left, 1.0))

    def record(self, rec: dict) -> None:
        rec["ts"] = datetime.now(timezone.utc).isoformat(timespec="seconds")
        try:
            with open(TRADE_LOG, "a", encoding="utf-8") as fh:
                fh.write(json.dumps(rec) + "\n")
        except OSError:
            pass

    def heartbeat(self, force: bool = False) -> None:
        if not force and time.time() - self.last_heartbeat < 300:
            return
        self.last_heartbeat = time.time()
        s = self.stats
        log.info("alive | scans %d | groups %d (%d with live quotes) | candidates %d | baskets filled %d | "
                 "missed %d | locked profit so far ~%.2f | buying power %.0f",
                 s["cycles"], len(self.groups), self.quoted, s["candidates"], s["filled"], s["misses"],
                 self.locked_profit, self.buying_power)
        if self.near:
            log.info("closest to an arbitrage (edge per set, must be above 0): %s",
                     "; ".join(f"{label[:45]} {edge / SCALE:+.3f}" for edge, label in self.near[:3]))

    def check_end(self) -> None:
        if self.t_end and datetime.now(timezone.utc) > self.t_end + timedelta(minutes=2):
            raise StopBot("The competition has ended - stopping the bot.", 0)

    def handle_api_error(self, e: ApiError) -> None:
        kind = classify(e)
        if kind == "fatal":
            raise StopBot(explain(e), 2)
        if kind == "wait":
            log.error("%s", explain(e))
            self.sleep(120)
            return
        self.errors += 1
        delay = min(5 * 2 ** min(self.errors, 5), 120) + random.random()
        log.warning("temporary problem: %s - waiting %.0fs", e, delay)
        self.sleep(delay)

    # -- start-up ----------------------------------------------------------

    def startup(self) -> None:
        acct = self.api.connect()
        log.info("connected to %s as %s", self.api.base, acct.get("username") or acct.get("id"))
        self.pick_tournament()
        if not self.cfg.dry_run:
            self.probe_trade_scope()
        self.refresh_account()
        log.info("balance %.2f | buying power %.2f | mode: %s", self.balance, self.buying_power,
                 "DRY RUN (no orders)" if self.cfg.dry_run else "LIVE")
        log.info("settings: min edge %.3f per share | min profit %.2f per basket | "
                 "max %.0f%% of buying power per basket",
                 self.cfg.min_edge_ticks / SCALE, self.cfg.min_basket_profit, self.cfg.max_cost_fraction * 100)
        self.refresh_universe()

    def pick_tournament(self) -> None:
        items: List[dict] = []
        offset = 0
        while True:
            j = self.api.request("GET", "/tournaments",
                                 params={"status": "active", "limit": 100, "offset": offset})
            items += j.get("data") or []
            if not (j.get("pagination") or {}).get("hasMore"):
                break
            offset += 100
        chosen: Optional[dict] = None
        wanted = self.cfg.tournament_slug
        if wanted:
            chosen = next((t for t in items if t.get("slug") == wanted), None)
            if chosen is None:
                log.warning("tournament %r is not among your active tournaments", wanted)
        if chosen is None:
            hint = self.cfg.tournament_hint.lower()
            matches = [t for t in items if hint in f"{t.get('name', '')} {t.get('slug', '')}".lower()]
            if matches:
                chosen = matches[0]
            elif items:
                chosen = items[0]
                if len(items) > 1:
                    log.warning("several active tournaments and none matches %r - using %r. Others: %s. "
                                "Set SUPERMARKET_TOURNAMENT=<slug> to choose.", hint, chosen.get("name"),
                                ", ".join(str(t.get("slug")) for t in items))
        if chosen is None:
            log.warning("no active tournament found - using the organization's default context")
            return
        self.tid = str(chosen.get("id"))
        self.t_slug = str(chosen.get("slug") or "")
        self.t_initial = to_float(chosen.get("initialBalance")) or 0.0
        self.t_name = str(chosen.get("name") or chosen.get("slug"))
        self.t_end = parse_dt(chosen.get("endDate"))
        log.info("tournament: %s (ends %s)", self.t_name, self.t_end.isoformat() if self.t_end else "n/a")
        if chosen.get("isPendingEnrolment"):
            log.info("not enrolled yet - your first order enrols you if the competition is open to you")

    def probe_trade_scope(self) -> None:
        """An empty basket is always rejected, but a key without the trade scope is refused first."""
        try:
            self.api.request("POST", "/orders/multi-leg",
                             body={"idempotencyKey": f"probe-{uuid.uuid4().hex}", "legs": []},
                             write=True, retry_429=False, max_attempts=1)
        except ApiError as e:
            if classify(e) in ("fatal", "wait"):
                raise
            log.debug("trade-scope probe answered %s (expected)", e.code)

    def refresh_account(self) -> None:
        j = self.api.request("GET", "/account", params=self.p())
        bal = j.get("balance")
        bp = j.get("buyingPower")
        self.balance = float(bal) if bal is not None else 0.0
        self.buying_power = float(bp) if bp is not None else self.balance
        self.last_account = time.time()

    def refresh_account_safe(self) -> None:
        try:
            self.refresh_account()
        except ApiError as e:
            if classify(e) != "retry":
                raise
            log.debug("account refresh failed: %s", e)

    # -- universe ----------------------------------------------------------

    def fetch_markets(self) -> List[dict]:
        out: List[dict] = []
        cursor: Optional[str] = None
        while True:
            params = self.p({"limit": 100, "status": "open"})
            if cursor:
                params["cursor"] = cursor
            j = self.api.request("GET", "/markets", params=params)
            out += j.get("data") or []
            page = j.get("pagination") or {}
            cursor = page.get("nextCursor")
            if not page.get("hasMore") or not cursor:
                break
        return out

    def fetch_relationships(self) -> List[dict]:
        out: List[dict] = []
        cursor: Optional[str] = None
        while True:
            params = self.p({"limit": 200})
            if cursor:
                params["cursor"] = cursor
            j = self.api.request("GET", "/relationships", params=params)
            out += j.get("data") or []
            page = j.get("pagination") or {}
            cursor = page.get("nextCursor")
            if not page.get("hasMore") or not cursor:
                break
        return out

    def get_root(self, market_id: str) -> Optional[dict]:
        if market_id in self.root_cache:
            return self.root_cache[market_id]
        try:
            j = self.api.request("GET", f"/markets/{market_id}/nodes", params=self.p())
        except ApiError as e:
            if classify(e) != "retry":
                raise
            log.debug("could not read the structure of market %s: %s", market_id, e)
            return None
        root = j.get("root") if isinstance(j, dict) else None
        self.root_cache[market_id] = root
        return root

    def build_groups(self, markets: List[dict]) -> Dict[str, Group]:
        labels: Dict[int, str] = {}
        market_ex: Dict[str, List[int]] = {}
        market_by_id: Dict[str, dict] = {}
        for m in markets:
            mid = str(m.get("id"))
            exs: List[int] = []
            for e in m.get("exchanges") or []:
                try:
                    eid = int(e["id"])
                except (KeyError, TypeError, ValueError):
                    continue
                exs.append(eid)
                labels[eid] = f"{m.get('title', '?')} [{e.get('option')}]"
            market_ex[mid] = exs
            market_by_id[mid] = m
        self.labels = labels
        ex_to_market = {eid: mid for mid, exs in market_ex.items() for eid in exs}

        groups: Dict[str, Group] = {}
        me_seen: Dict[frozenset, str] = {}
        skipped: Counter = Counter()

        def whole_market(ids: List[int]) -> Optional[str]:
            mids = {ex_to_market[i] for i in ids}
            if len(mids) == 1:
                mid = next(iter(mids))
                if set(market_ex[mid]) == set(ids):
                    return mid
            return None

        def add_me(gid: str, label: str, ids: List[int], exhaustive: bool, source: str) -> None:
            key = frozenset(ids)
            combos = me_combos(len(ids), exhaustive)
            old = me_seen.get(key)
            if old is not None:
                if len(combos) < len(groups[old].combos):      # the more cautious reading wins
                    groups[old].combos = combos
                return
            me_seen[key] = gid
            groups[gid] = Group(gid, label, list(ids), combos, whole_market(ids), source)

        # 1) the platform's own relationship graph
        try:
            rels = self.fetch_relationships()
        except ApiError as e:
            if classify(e) != "retry":
                raise
            log.warning("could not read the relationship graph (%s) - continuing without it", e)
            rels = []

        for rel in rels:
            if rel.get("status", "active") != "active":
                continue
            try:
                ids = [int(n["exchangeId"]) for n in rel.get("nodes") or []]
            except (KeyError, TypeError, ValueError):
                continue
            rtype = str(rel.get("type"))
            if len(ids) < 2 or len(set(ids)) != len(ids) or any(i not in ex_to_market for i in ids):
                continue
            gid = f"REL:{rel.get('id')}"
            label = str(rel.get("label") or rtype)
            if rtype in ("mutually_exclusive", "complementary"):
                if len(ids) > MAX_LEGS or (rtype == "complementary" and len(ids) != 2):
                    skipped[f"{rtype} (size)"] += 1
                    continue
                exhaustive = True if rtype == "complementary" else bool(rel.get("isExhaustive"))
                add_me(gid, label, ids, exhaustive, "engine-set")
                continue
            if len(ids) > MAX_GENERIC_NODES:
                skipped[f"{rtype} (too many contracts)"] += 1
                continue
            ckey = (str(rel.get("id")), rel.get("version"), tuple(ids))
            combos = self.combo_cache.get(ckey)
            if combos is None:
                try:
                    pred = build_predicate(rel, ids)
                    combos = combos_from_predicate(ids, pred) if pred is not None else []
                except (KeyError, TypeError, ValueError):
                    pred, combos = None, []
                if pred is None:
                    skipped[f"{rtype} (unsupported)"] += 1
                self.combo_cache[ckey] = combos
            if combos:
                groups[gid] = Group(gid, label, ids, combos, None, "logic")

        # 2) plain multi-outcome markets the graph did not cover: exactly one outcome wins
        if self.cfg.structural_me:
            announced = False
            for mid, m in market_by_id.items():
                exs = market_ex[mid]
                if not (2 <= len(exs) <= MAX_LEGS) or frozenset(exs) in me_seen:
                    continue
                if not m.get("isMultiOutcome") or m.get("isComposite"):
                    continue
                if any("import" in str(c).lower() for c in m.get("categories") or []):
                    continue
                last = [e.get("latestPrice") for e in m.get("exchanges") or []]
                if all(x is not None for x in last) and not 0.5 <= sum(float(x) for x in last) <= 1.6:
                    continue          # prices say these outcomes are not mutually exclusive
                if mid not in self.root_cache and not announced:
                    log.info("reading the structure of multi-outcome markets (first run only, can take a minute)")
                    announced = True
                root = self.get_root(mid)
                if not root or root.get("node_type") != "contract":
                    continue
                if str(root.get("contract_type")) in ("Imported Market", "Existing Market"):
                    continue
                add_me(f"MKT:{mid}", str(m.get("title", mid)), exs, True, "market")

        if skipped:
            log.info("relationships skipped: %s", dict(skipped))
        return groups

    def refresh_universe(self) -> None:
        markets = self.fetch_markets()
        groups = self.build_groups(markets)
        for gid in list(self.cooldown):
            if gid not in groups:
                del self.cooldown[gid]
        self.groups = groups
        watch = {e for g in groups.values() for e in g.exch}
        if self.follower is not None:
            watch |= self.follower.exchange_ids()
        self.watch = sorted(watch)
        reads = max(1, math.ceil(len(self.watch) / 100))
        self.cycle_seconds = max(self.cfg.cycle_seconds,
                                 reads * 60.0 / max(self.cfg.read_budget - 20, 10))
        self.last_universe = time.time()
        kinds = Counter(g.source for g in groups.values())
        log.info("universe: %d open markets | groups: %s | %d exchanges watched | scan every %.0fs",
                 len(markets), dict(kinds) or "none", len(self.watch), self.cycle_seconds)
        if not self.listed:
            self.listed = True
            for g in groups.values():
                log.debug("group %s [%s] %s -> exchanges %s", g.gid, g.source, g.label[:70], g.exch)

    # -- market data -------------------------------------------------------

    def fetch_quotes(self) -> Dict[int, Tuple[Optional[int], Optional[int]]]:
        out: Dict[int, Tuple[Optional[int], Optional[int]]] = {}
        for i in range(0, len(self.watch), 100):
            chunk = self.watch[i:i + 100]
            j = self.api.request("GET", "/exchanges/prices",
                                 params=self.p({"ids": ",".join(str(e) for e in chunk)}))
            for row in j.get("data") or []:
                try:
                    eid = int(row["exchangeId"])
                except (KeyError, TypeError, ValueError):
                    continue
                out[eid] = (to_ticks(row.get("bestBid")), to_ticks(row.get("bestAsk")))
        return out

    def fetch_books(self, g: Group) -> Dict[int, Book]:
        books: Dict[int, Book] = {}
        if g.market_id:
            j = self.api.request("GET", f"/markets/{g.market_id}/orderbook",
                                 params=self.p({"depth": self.cfg.depth}))
            rows = None
            for c in j.get("contexts") or []:
                if self.tid and (c.get("tournament") or {}).get("id") == self.tid:
                    rows = (c.get("orderbook") or {}).get("exchanges")
                    break
            if rows is None:
                rows = j.get("exchanges") or []
            for row in rows:
                try:
                    books[int(row["exchangeId"])] = make_book(row.get("bids"), row.get("asks"))
                except (KeyError, TypeError, ValueError):
                    continue
        else:
            for eid in g.exch:
                j = self.api.request("GET", f"/exchanges/{eid}/orderbook",
                                     params=self.p({"depth": self.cfg.depth}))
                books[eid] = make_book(j.get("bids"), j.get("asks"))
        return books

    # -- scanning ----------------------------------------------------------

    def quote_edge(self, g: Group, quotes: Dict[int, Tuple[Optional[int], Optional[int]]]) -> Optional[int]:
        """Best per-set edge in ticks (negative = no arbitrage) using best prices only.
        None if a quote needed by every basket is missing."""
        books: Dict[int, Book] = {}
        for eid in g.exch:
            quote = quotes.get(eid)
            if quote is None:
                return None
            bid, ask = quote
            books[eid] = Book([(bid, BIG)] if bid else [], [(ask, BIG)] if ask else [])
        best: Optional[int] = None
        for combo in g.combos:
            plan = plan_combo(g, combo, books, -BIG, 1, BIG * SCALE)
            if plan is not None and (best is None or plan.profit_ticks > best):
                best = plan.profit_ticks
        return best

    def warn_once(self, g: Group, edge_ticks: int) -> None:
        if time.time() - self.warned.get(g.gid, 0.0) > 3600:
            self.warned[g.gid] = time.time()
            log.warning("skipping %s: an edge of %.3f per set looks too good to be true "
                        "(check that relationship on the site)", g.label[:70], edge_ticks / SCALE)

    def scan(self) -> None:
        now = time.time()
        if now - self.last_universe > self.cfg.universe_refresh_seconds:
            self.refresh_universe()
        if now - self.last_account > self.cfg.account_refresh_seconds:
            self.refresh_account()
        if not self.watch:
            return
        quotes = self.fetch_quotes()
        self.stats["cycles"] += 1
        if self.groups:
            self.scan_arbitrage(quotes)
        if self.follower is not None:
            try:
                self.follower.step(quotes)
                self.follower.errors = 0
            except (ApiError, StopBot):
                raise
            except Exception:
                log.exception("follow strategy error (arbitrage keeps running)")
                self.follower.errors += 1
                if self.follower.errors >= 5:
                    log.error("follow strategy switched off after repeated errors")
                    self.follower.active = False

    def scan_arbitrage(self, quotes: Dict[int, Tuple[Optional[int], Optional[int]]]) -> None:
        now = time.time()

        quoted: List[Tuple[int, Group]] = []
        candidates: List[Tuple[int, Group]] = []
        for g in self.groups.values():
            edge = self.quote_edge(g, quotes)
            if edge is None:
                continue
            quoted.append((edge, g))
            if edge < self.cfg.min_edge_ticks or self.cooldown.get(g.gid, 0.0) > now:
                continue
            if edge > self.cfg.max_plausible_edge * SCALE:
                self.warn_once(g, edge)
                self.cooldown[g.gid] = now + 600
                continue
            candidates.append((edge, g))
        quoted.sort(key=lambda item: -item[0])
        self.quoted = len(quoted)
        self.near = [(edge, g.label) for edge, g in quoted[:5]]
        if self.buying_power < 5.0 or not candidates:
            return

        cap = min(self.cfg.max_basket_cost, self.cfg.max_cost_fraction * self.buying_power)
        max_cost_ticks = int(cap * SCALE)
        candidates.sort(key=lambda item: -item[0])

        plans: List[Plan] = []
        for edge, g in candidates[: self.cfg.max_candidates_per_cycle]:
            self.stats["candidates"] += 1
            try:
                books = self.fetch_books(g)
            except ApiError as e:
                if classify(e) != "retry":
                    raise
                log.debug("order book read failed for %s: %s", g.label[:50], e)
                self.cooldown[g.gid] = time.time() + 30
                continue
            plan = best_plan(g, books, self.cfg.min_edge_ticks, self.cfg.max_sets, max_cost_ticks)
            if plan is None or plan.profit < self.cfg.min_basket_profit:
                self.cooldown[g.gid] = time.time() + 30
                log.debug("nothing worth taking in %s (price edge %.3f per set)", g.label[:50], edge / SCALE)
                continue
            plans.append(plan)

        plans.sort(key=lambda pl: -pl.profit_ticks)
        used: Set[int] = set()
        for plan in plans:
            ids = {eid for eid, _ in plan.legs}
            if ids & used or plan.cost > self.buying_power * 0.98:
                continue
            self.execute(plan)
            used |= ids

    # -- orders ------------------------------------------------------------

    def execute(self, plan: Plan) -> str:
        g = plan.group
        self.seq += 1
        key = f"sigarb-{self.run_id}-{self.seq}-{uuid.uuid4().hex[:8]}"
        legs: List[dict] = []
        for (eid, sign), limit in zip(plan.legs, plan.limits):
            leg = {
                "exchangeId": str(eid),
                "side": "yes" if sign > 0 else "no",
                "action": "buy",
                "quantity": int(plan.qty),
                "price": ticks_to_price(limit),
            }
            if self.tid:
                leg["tournamentId"] = self.tid
            legs.append(leg)
        parts = []
        for (eid, sign), limit in zip(plan.legs, plan.limits):
            name = self.label(eid)[:45]
            parts.append(f"{'YES' if sign > 0 else 'NO'} {name} @ {ticks_to_price(limit):.3f}")
        summary = (f"{g.label[:60]} :: qty {plan.qty}, cost {plan.cost:.2f}, expected profit "
                   f"+{plan.profit:.2f} (at least +{plan.worst_profit:.2f}) :: " + " | ".join(parts))
        if self.cfg.dry_run:
            log.info("DRY RUN, would place: %s", summary)
            self.stats["dry_run"] += 1
            self.cooldown[g.gid] = time.time() + 60
            return "dry"

        log.info("PLACING: %s", summary)
        body = {"idempotencyKey": key, "executionMode": "allOrNone", "legs": legs}
        try:
            resp = self.api.request("POST", "/orders/multi-leg", body=body, write=True,
                                    retry_429=False, max_attempts=3, max_wait=3.0)
        except ApiError as e:
            return self.on_order_error(plan, e)

        results = resp.get("results") or []
        traded: List[float] = []
        cost = 0.0
        for r in results:
            d = (r or {}).get("data") or {}
            traded.append(float(d.get("quantityTraded") or 0.0))
            cost += float(d.get("totalCost") or 0.0)
        complete = len(results) == len(legs) and all(t + 1e-9 >= plan.qty for t in traded)
        locked = plan.floor * plan.qty - cost
        self.cooldown[g.gid] = time.time() + 5
        self.record({
            "group": g.gid, "label": g.label, "qty": plan.qty, "legs": legs, "cost": round(cost, 4),
            "floor_payout": plan.floor * plan.qty, "locked_profit": round(locked, 4),
            "planned_profit": round(plan.profit, 4), "complete": complete,
        })
        if not complete:
            log.warning("basket reported partial fills %s - check your positions on the site", traded)
            self.stats["partial"] += 1
            self.refresh_account_safe()
            return "partial"

        self.stats["filled"] += 1
        self.locked_profit += locked
        log.info("FILLED: qty %d, cost %.2f, locked profit %.2f (planned %.2f)",
                 plan.qty, cost, locked, plan.profit)
        if locked < -max(1.0, 0.005 * cost):
            self.bad_fills += 1
            log.warning("locked profit came out negative (%.2f) - check this trade on the site", locked)
            if self.bad_fills >= 2:
                raise StopBot("Two trades in a row came out unprofitable, stopping to be safe. "
                              "Look at sig_arb_trades.jsonl.", 3)
        else:
            self.bad_fills = 0
        self.refresh_account_safe()
        return "filled"

    def on_order_error(self, plan: Plan, e: ApiError) -> str:
        g = plan.group
        if classify(e) in ("fatal", "wait"):
            raise e
        if e.status == 400 and "executionMode" in e.details:
            raise StopBot("This competition does not accept all-or-none baskets, so the bot cannot trade "
                          "safely here. Details: " + e.message, 4)
        if e.status == 400 and e.details.get("rejectionReasonCode") == "AllOrNoneNotFilled":
            log.info("basket missed (liquidity moved): %s", g.label[:70])
            self.stats["misses"] += 1
            self.cooldown[g.gid] = time.time() + 10
            return "miss"
        if e.code == "LOCAL_RATE_LIMIT" or e.status == 429:
            log.info("order not sent (rate limit): %s", e.code)
            self.cooldown[g.gid] = time.time() + 5
            return "throttled"
        log.warning("order rejected for %s: %s", g.label[:60], e)
        self.stats["rejected"] += 1
        self.cooldown[g.gid] = time.time() + 60
        if e.status in (0, 409, 502, 503):        # outcome may be unknown, re-read the balance
            self.refresh_account_safe()
        return "error"

    # -- main loop ---------------------------------------------------------

    def list_markets(self) -> int:
        """Write every open SIG market and exchange to sig_markets.csv, for matching with outside markets."""
        try:
            self.api.connect()
            self.pick_tournament()
            markets = self.fetch_markets()
            self.watch = sorted({int(e["id"]) for m in markets for e in m.get("exchanges") or []
                                 if str(e.get("id", "")).isdigit()})
            quotes = self.fetch_quotes()
        except ApiError as e:
            log.error("%s", explain(e))
            return 2
        rows = 0
        with open(MARKETS_CSV, "w", newline="", encoding="utf-8-sig") as fh:
            out = csv.writer(fh)
            out.writerow(["market_id", "market_title", "exchange_id", "option", "best_bid", "best_ask",
                          "last_price", "multi_outcome", "composite", "closes"])
            for m in markets:
                for e in m.get("exchanges") or []:
                    if not str(e.get("id", "")).isdigit():
                        continue
                    bid, ask = quotes.get(int(e["id"]), (None, None))
                    last = e.get("latestPrice")
                    out.writerow([m.get("id"), m.get("title"), e.get("id"), e.get("option"),
                                  "" if bid is None else ticks_to_price(bid),
                                  "" if ask is None else ticks_to_price(ask),
                                  "" if last is None else last,
                                  m.get("isMultiOutcome"), m.get("isComposite"), m.get("settlementDate")])
                    rows += 1
        log.info("wrote %d rows to %s", rows, MARKETS_CSV)
        log.info("Upload that file to the chat and I will match the markets with Polymarket / Kalshi.")
        return 0

    def run(self) -> int:
        failures = 0
        while not self.ready:
            try:
                self.startup()
                self.ready = True
            except ApiError as e:
                self.handle_api_error(e)
            except StopBot:
                raise
            except Exception:
                failures += 1
                log.exception("unexpected error while starting up (%d of 5)", failures)
                if failures >= 5:
                    raise StopBot("Start-up keeps failing. See sig_arb_bot.log for the details.", 2)
                self.sleep(15)
        while True:
            started = time.time()
            try:
                self.check_end()
                self.scan()
                self.errors = 0
            except ApiError as e:
                self.handle_api_error(e)
            except StopBot:
                raise
            except Exception:
                log.exception("unexpected error in the scan loop")
                self.errors += 1
                self.sleep(min(5 * self.errors, 60))
            self.heartbeat()
            if self.cfg.once:
                return 0
            self.sleep(self.cycle_seconds - (time.time() - started))


# ---------------------------------------------------------------------------
# entry point
# ---------------------------------------------------------------------------

def selftest() -> int:
    """Offline checks of the maths. Needs no network and no key."""
    problems: List[str] = []

    def check(name: str, ok: bool) -> None:
        print(("ok    " if ok else "FAIL  ") + name)
        if not ok:
            problems.append(name)

    check("tick conversion",
          to_ticks(0.545) == 109 and to_ticks(1) is None and ticks_to_price(109) == 0.545)

    # a complete set bought across three outcomes, walking the books
    levels = [[(60, 100), (62, 500)], [(64, 200)], [(66, 50), (70, 500)]]
    check("complete-set sizing",
          size_levels(levels, SCALE, 1, 10 ** 6, 10 ** 12) == (200, [62, 64, 70], 38800, 1200))

    # NO on every outcome when the YES bids add up to more than 1
    bids = [[(70, 100)], [(66, 100)], [(68, 100)]]
    no_levels = [[(SCALE - p, q) for p, q in lv] for lv in bids]
    check("NO-side sizing",
          size_levels(no_levels, 2 * SCALE, 1, 10 ** 6, 10 ** 12) == (100, [130, 134, 132], 39600, 400))

    # implication A -> B: only "NO on A + YES on B" pays at least 1 whatever happens
    imp = combos_from_predicate([1, 2], lambda s: not (s[1] and not s[2]))
    check("implication basket", [(c.signs, c.floor) for c in imp] == [((-1, 1), 1)])

    # C = A and B
    land = combos_from_predicate([10, 11, 12], lambda s: bool(s[10]) == bool(s[11] and s[12]))
    check("AND baskets", {c.signs for c in land} == {(-1, 1, 0), (-1, 0, 1), (1, -1, -1)}
          and all(c.floor == 1 for c in land))

    # fake books: A bid 0.60, B ask 0.50 with A -> B is a 0.10 edge per set
    g = Group("t", "test", [1, 2], imp)
    books = {1: Book([(120, 80)], [(124, 80)]), 2: Book([(98, 80)], [(100, 80)])}
    plan = best_plan(g, books, 1, 1000, 10 ** 9)
    check("pair arbitrage found",
          plan is not None and plan.qty == 80 and plan.legs == [(1, -1), (2, 1)]
          and plan.limits == [80, 100] and plan.profit_ticks == 80 * 20)

    # follow strategy: outside price 0.70 against a SIG market quoted 0.59 / 0.61
    cfg = Config()
    it = follow_intent(0.70, 118, 122, cfg, 100000.0, 0.0)
    check("follow buys YES when SIG is cheap",
          it is not None and it.side == "yes" and 7000 < it.shares < 9000 and it.max_price >= 122)
    check("follow does not double up", follow_intent(0.70, 118, 122, cfg, 100000.0, 9000.0) is None)
    it = follow_intent(0.40, 118, 122, cfg, 100000.0, 0.0)
    check("follow buys NO when SIG is rich", it is not None and it.side == "no" and 11000 < it.shares < 13000)
    check("follow ignores small gaps", follow_intent(0.62, 118, 122, cfg, 100000.0, 0.0) is None)
    fill = follow_fill(Book([], [(120, 100), (124, 300)]), Intent("yes", 0.7, 0.08, 122, 250))
    check("follow walks the book", fill == (100, 120, 60.0))
    two = [ExtQuote(0.60, 0.02, 10000.0, "a"), ExtQuote(0.62, 0.04, 20000.0, "b")]
    mean = combine_quotes(two, 5000.0, 0.12)
    check("outside prices combine", mean is not None and abs(mean - 0.61) < 1e-9)
    apart = [ExtQuote(0.50, 0.02, 10000.0, "a"), ExtQuote(0.70, 0.02, 10000.0, "b")]
    check("outside sources that disagree are skipped", combine_quotes(apart, 5000.0, 0.12) is None)

    print("all checks passed" if not problems else f"{len(problems)} check(s) failed")
    return 1 if problems else 0


def load_key() -> str:
    key = os.environ.get("SUPERMARKET_API_KEY", "").strip()
    if not key and KEY_FILE.exists():
        try:
            key = KEY_FILE.read_text(encoding="utf-8-sig").strip()
        except OSError:
            key = ""
    if not key:
        key = API_KEY_IN_FILE.strip()
    return (key.splitlines() or [""])[0].strip().strip("\"'")


def setup_logging(verbose: bool) -> None:
    log.setLevel(logging.DEBUG)
    fmt = logging.Formatter("%(asctime)s %(levelname)-7s %(message)s", "%Y-%m-%d %H:%M:%S")
    console = logging.StreamHandler(sys.stdout)
    console.setLevel(logging.DEBUG if verbose else logging.INFO)
    console.setFormatter(fmt)
    log.addHandler(console)
    try:
        logfile = logging.handlers.RotatingFileHandler(LOG_FILE, maxBytes=2_000_000,
                                                       backupCount=3, encoding="utf-8")
        logfile.setLevel(logging.DEBUG)
        logfile.setFormatter(fmt)
        log.addHandler(logfile)
    except OSError:
        pass


def keep_awake(on: bool) -> None:
    """Ask Windows not to sleep while the bot runs."""
    if os.name != "nt":
        return
    try:
        import ctypes
        es_continuous, es_system_required = 0x80000000, 0x00000001
        flags = (es_continuous | es_system_required) if on else es_continuous
        ctypes.windll.kernel32.SetThreadExecutionState(flags)
    except Exception:
        pass


def main() -> int:
    if sys.version_info < (3, 8):
        print("Python 3.8 or newer is required.")
        return 2
    try:
        sys.stdout.reconfigure(errors="replace")      # type: ignore[attr-defined]
    except Exception:
        pass

    ap = argparse.ArgumentParser(description="SIG Super Market arbitrage bot")
    ap.add_argument("--dry-run", action="store_true", help="find and print baskets, place nothing")
    ap.add_argument("--once", action="store_true", help="run a single scan and exit")
    ap.add_argument("--selftest", action="store_true", help="offline check of the maths, no key needed")
    ap.add_argument("--follow", action="store_true",
                    help="also trade toward Polymarket / Kalshi prices (needs follow_map.json)")
    ap.add_argument("--list-markets", action="store_true",
                    help="write all open SIG markets to sig_markets.csv and exit")
    ap.add_argument("--verbose", "-v", action="store_true", help="more console output")
    ap.add_argument("--tournament", default=os.environ.get("SUPERMARKET_TOURNAMENT", ""),
                    help="tournament slug (default: auto-detect the Midterm competition)")
    args = ap.parse_args()
    if args.selftest:
        return selftest()

    cfg = Config(dry_run=args.dry_run, once=args.once, verbose=args.verbose,
                 tournament_slug=args.tournament.strip(), follow=args.follow)
    base = os.environ.get("SUPERMARKET_BASE_URL", "").strip()
    if base:
        cfg.base_urls = [base.rstrip("/")]
    cfg.api_key = load_key()

    setup_logging(cfg.verbose)
    if not cfg.api_key:
        log.error("No API key found. Save it in api_key.txt next to this script "
                  "(or set SUPERMARKET_API_KEY).")
        return 2

    bot = Bot(cfg)
    if args.list_markets:
        return bot.list_markets()
    keep_awake(True)
    code = 0
    try:
        code = bot.run()
    except StopBot as stop:
        (log.info if stop.code == 0 else log.error)("%s", stop)
        code = stop.code
    except KeyboardInterrupt:
        log.info("stopped by user")
    finally:
        keep_awake(False)
        bot.heartbeat(force=True)
    return code


if __name__ == "__main__":
    sys.exit(main())
