# Susquehanna Prediction Cup – Arbitrage Bot

A Python bot I built for the SIG Super Market **Midterm Elections** prediction competition.

The core idea is simple: **no forecasting, no news.** The bot only takes trades where prices across related contracts are inconsistent, so the basket pays off *no matter which outcome happens*. An optional second strategy ("follow") compares SIG prices against Polymarket and Kalshi. That part is not risk-free.

---

## My process

### 1. Find guaranteed-profit baskets

Prediction market contracts pay 1.00 if they resolve YES and 0 otherwise. When several contracts are logically linked, their prices *should* be consistent. When they aren't, there's free money.

**Complete sets.** In a market where exactly one outcome wins:

| Condition | Trade | Why it works |
|---|---|---|
| Sum of best YES **asks** < 1 | Buy YES on every outcome | Exactly one pays 1, so you paid less than you get back |
| Sum of best YES **bids** > 1 | Buy NO on every outcome | All but one pay 1 |

**Logical links.** The platform publishes a relationship graph between contracts (implication, AND / OR / NOT, mutually exclusive, boolean expressions). For groups of up to 6 linked contracts, the bot:

1. Lists every YES/NO combination the logic allows (e.g. for *A implies B*, "A YES and B NO" is impossible).
2. Tries every basket of YES / NO / skip on each contract.
3. Computes the **worst-case payout** of each basket across all allowed outcomes.
4. Keeps only baskets with a worst case of at least 1 share and no useless legs.

Example: if *A implies B*, then "buy NO on A + buy YES on B" always pays at least 1. If those two cost less than 1.00 combined, that's a locked profit.

### 2. Size the trade by walking the order book

Instead of just using the best price, the bot walks down every leg's order book together. It keeps adding sets as long as each extra set still earns at least the minimum edge (1 tick = 0.005). Each basket is also capped at a share of buying power (25% by default, max 25,000).

### 3. Execute atomically

Every basket is sent as one **all-or-none multi-leg order**. Either every leg fills at the limit prices or nothing executes. This means there is never a half-filled basket that leaves me exposed, and no resting orders are left on the book.

### 4. Safety checks

- Edges that look too good (over 0.30 per set) are treated as a probable modelling error and skipped.
- If two trades in a row come out unprofitable, the bot stops itself.
- Stays under the platform rate limits (100 reads / 30 writes per minute).
- Relationship types that can't be modelled safely (IF, ladders without direction) are skipped.
- Stops automatically when the competition ends.

### 5. Optional: follow strategy (`--follow`)

This part **can lose money**. For market pairs I've matched by hand (in `follow_map.json`), it compares SIG prices with Polymarket / Kalshi. When SIG is mispriced by at least 4 cents against a blended fair value, it buys the cheap side.

Risk controls:
- Fractional Kelly sizing (30% of Kelly)
- At most 5% of account value per market (12% when the outcome looks near-certain), 50% in total
- Ignores thin markets, sources that disagree with each other, stale prices and sudden one-read spikes
- Turns itself off if the account drops 35% below its starting value

---

## Setup

Requires Python 3.8+.

```
pip install requests
```

Put your API key (needs **both** `read` and `trade` scopes) in a file called `api_key.txt` next to the script, **or** set an environment variable:

```
set SUPERMARKET_API_KEY=your_key_here
```

> ⚠️ Never commit `api_key.txt`. It's listed in `.gitignore`. Leave `API_KEY_IN_FILE` in the script empty.

## Usage

```
python sig_arb_bot.py --selftest                  # offline check of the maths, no key needed
python sig_arb_bot.py --dry-run --once            # show what it finds, place nothing
python sig_arb_bot.py                             # live arbitrage
python sig_arb_bot.py --list-markets              # export open markets to sig_markets.csv
python sig_arb_bot.py --follow --dry-run --once   # preview the follow strategy
python sig_arb_bot.py --follow                    # live: arbitrage + follow
```

Other flags: `--verbose`, `--tournament <slug>`. Stop any time with Ctrl+C.

All settings (edges, caps, polling intervals) are in the `Config` class at the top of the script.

## Output files (not committed)

- `sig_arb_bot.log` – full log
- `sig_arb_trades.jsonl` – one line per trade
- `sig_markets.csv` – market export from `--list-markets`

## Known limits

- If a market is cancelled / resolved N/A, it's refunded at cost, which can break the guarantee on a cross-market basket. Rare but possible.
- Some relationship types aren't modelled and are skipped.
- Follow strategy depends on correct market matching in `follow_map.json`.

## Disclaimer

Built for a competition using play money (SUSQies). Not financial advice.
