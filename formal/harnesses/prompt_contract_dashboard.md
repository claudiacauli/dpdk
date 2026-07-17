# DPDK Formal Verification Contract Visualizer — Interactive Dashboard

## 1. Project Context

I am a Formal Methods Research Engineer verifying the DPDK (Data Plane Development Kit) BPF validator (`lib/bpf/bpf_validate.c`) using assume-guarantee reasoning with Frama-C/WP, CBMC, and ESBMC. I have completed verification of the `eval_alu()` dispatcher method and all its downstream callees (22 harnesses total).

Each harness lives under `formal/harnesses/<method_name>/` and contains:
- `<method>.c` — Frama-C/WP proof file with ACSL contract (`requires`, `ensures`, `assigns`, `terminates`) and in-function `/*@ assert */` stepping stones
- `<method>.h` — Header with ACSL predicates (soundness predicates, auxiliary logic)
- `<method>_bmc.c` — CBMC/ESBMC bounded model checking harness
- `<method>_main.c` — WP main entry point
- `axioms_*.h` — Per-harness quantified lemmas (included from `.c` only)
- `README.md` — Verification notes

## 2. What Already Exists

Two interactive HTML files have been built:

**A) Call Graph** (`eval_alu_call_graph.html`):
- 25 nodes organized in 5 levels (0: entry, 1: pre-processing, 2: operator dispatch, 3: helpers/overflow, 4: bit helpers)
- Force-directed auto-layout with level Y constraints
- Drag-and-drop nodes, canvas pan, save/load layout, edge curve dragging
- Each node shows method name (bold) + parameters

**B) Control Flow Graph** (`eval_alu_control_flow_graph.html`):
- Flowchart of eval_alu() body: entry -> setup -> branch (X/K) -> mask -> self-xor -> defined -> err? -> dispatch -> operators -> exit
- Draggable nodes and edges, curved bezier routing, save/load layout

Both use vanilla JS, SVG, no dependencies.

Also available:
- `eval_alu_call_graph.dot` — Complete edge list in DOT format (machine-parseable, contains all call relationships)

## 3. The Verification Architecture (What Needs Visualizing)

### 3.1 Method Categories

**3.1.1 Operator Harnesses** (prove unsigned_soundness + signed_soundness):
`eval_add`, `eval_sub`, `eval_and`, `eval_or`, `eval_xor`, `eval_mul`, `eval_divmod`, `eval_neg`, `eval_lsh`, `eval_rsh`, `eval_arsh`

Each contract has: `requires` (preconditions like `range_ordering`, `range_within_width`, `is_scalar`, `\separated`), `ensures` (`type_ok`, `uord/sord`, `uwidth/swidth`, `usound`, `ssound`), `assigns`, `terminates`.

**3.1.2 Bound Helpers** (no soundness predicates — pure functional):
`eval_max_bound`, `eval_umax_bound`, `eval_smax_bound`, `eval_fill_max_bound`, `eval_fill_imm`, `eval_fill_imm64`, `eval_umax_bits`, `eval_uand_max`, `eval_uor_max`, `eval_defined`

**3.1.3 Pre-processing Helpers**:
`eval_apply_mask` (has `wsound` witness-transport predicate), `eval_fill_imm`/`eval_fill_imm64`

**3.1.4 The Dispatcher**:
`eval_alu` — orchestrates all of the above. Its `usound`/`ssound` are **PARKED** (proved but quarantined due to heap plumbing not closing). The 12 unsigned composition lemmas (`axioms_alu.h`) are machine-proved (~3s each) but not fed to the dispatcher goals. The 12 signed twins (`axioms_alu_signed.h`) are stated but UNPROVED (low-bit congruence bridge missing).

### 3.2 Fix Gates

Many harnesses have `#ifdef FIX_*` macros for verified bug fixes. These are controlled by a master switch `ALL_FIXES` in `formal/common/fixes.h`. When the FIX is enabled, the proof passes; when disabled, the corresponding `ensures` fails. Current fix gates:

| Harness | Fix Gate | What It Fixes |
|---|---|---|
| eval_add | FIX_ADD_SIGNED_32 | 32-bit signed overflow canonicalization |
| eval_sub | FIX_SUB_SIGNED_32 | Same for subtraction |
| eval_and | FIX_AND_SIGNED_GUARD | One-sided non-negative bound |
| eval_mul | FIX_MUL_UGUARD | Unsigned overflow guard (`>> opsz` UB) |
| eval_mul | FIX_MUL_SCONST | Sign-extend constant product |
| eval_mul | FIX_MUL_SGUARD | Missing signed overflow guard |
| eval_divmod | FIX_DIVMOD_SIGNED_32 | Sign-boundary test for 32-bit |
| eval_neg | FIX_NEG_SIGNED_32 | Pattern vs canonical for 32-bit |
| eval_fill_imm64 | FIX_FILL_IMM_SIGNED_32 | Same |
| eval_umax_bits | FIX_UMAX_BITS_32 | Shift UB when opsz=32 |
| eval_apply_mask | FIX_APPLY_MASK_SIGNED | Signed range escape widening |
| eval_apply_mask | FIX_APPLY_MASK_CONSIST | Cross-track consistency repair |
| eval_arsh | FIX_ARSH_UNSIGNED_SIGN | Sign-extend unsigned patterns |
| eval_arsh | FIX_ARSH_32EXT_SHL | UB on negative left shift |
| eval_arsh | FIX_ARSH_SIGNED_MASK | 32-bit mask sign-extension |

### 3.3 Proof Status Categories

Each method has one of these statuses:
- **PROVED** — All ensures close in the WP proof with the current FIX configuration
- **PROVED_WITH_FIX** — Proved only when the FIX_* gate is enabled (upstream code without the fix would fail)
- **PARKED** — The lemmas are proved but not wired into the dispatcher contract (eval_alu's usound/ssound)
- **STATED_UNPROVED** — The lemma exists but the proof does not close (signed composition lemmas in axioms_alu_signed.h)
- **BM_ONLY** — No WP proof, only BMC harness exists (none in this project — all have WP proofs)

### 3.4 Contract Flow Architecture

The key insight to communicate: **contracts propagate through the call chain**.

For example, `eval_add` requires `range_validity` + `range_within_width` on both operands. Its ensures include `eval_add_unsigned_soundness`. This feeds into `eval_alu`'s unsigned composition lemma `alu_compose_add_u`, which requires `alu_wit_covers` (from `eval_apply_mask`) and `eval_add_unsigned_soundness` to conclude `eval_alu_unsigned_soundness`.

The "witness transport chain" is: register state -> `eval_apply_mask` (wsound: pre-mask witness -> post-mask witness) -> operator soundness (post-mask witness bounds the result pattern) -> dispatcher composition (pre-mask witness -> result pattern bounded).

## 4. What Network Engineers Need to Understand

Network engineers are NOT formal methods experts. They need:

1. **"What has been proved?"** — At a glance, which methods are verified, which have known bugs (FIX gates), and what's still pending
2. **"How do the contracts connect?"** — When I call `eval_add`, what assumptions does it make? What guarantees does it provide? How does that help `eval_alu`?
3. **"What are the FIX gates?"** — What bugs were found? What code paths would be wrong without the fix?
4. **"What does 'soundness' mean?"** — In visual terms: the unsigned track bounds the bit pattern, the signed track bounds its canonical interpretation
5. **"What is the verification status of the full eval_alu path?"** — The dispatcher is the entry point; operators are proved; helpers are proved; composition lemmas exist but aren't wired

## 5. Desired Interactive Visualization Features

### 5.1 Multi-View Dashboard

Three linked views that communicate via shared state:

**View A: Contract Call Graph** (enhanced version of the existing call graph)
- Same node/layout as the call graph, but each node is color-coded by proof status (green=proved, yellow=proved_with_fix, red=unproved, gray=parked)
- Clicking a node shows its full contract in a side panel (requires, ensures, assigns, fix gates)
- Edges are labeled with the contract flow: what `requires` flows from caller to callee, what `ensures` flows back
- Filter by status, by has_fix, by type (operator/helper/dispatcher)

**View B: Contract Propagation Chain** (new)
- Select a specific operator (e.g., `eval_add`) and see the chain:
  - What preconditions must hold before calling it
  - Which callers satisfy those preconditions
  - What postconditions it guarantees
  - Which callees it calls and how their contracts compose
- Animate the flow: "requires flow down the call tree, ensures flow back up"
- Show the witness transport chain visually: register -> apply_mask (wsound) -> operator (usound/ssound) -> composition

**View C: Fix Gate Explorer** (new)
- List all FIX_* gates with their status (enabled/disabled in current build)
- For each gate, show: what contract ensures fail without the fix, the BMC counterexample description, the fix code snippet
- Toggle a fix on/off to see which proofs break

### 5.2 Interactive Features

- Drag-and-drop nodes (existing)
- Click-to-inspect contract panel (side panel or modal)
- Hover tooltip showing method name, status, and a one-line summary
- Search/filter bar (text search on method names, filter by status, by fix gate, by type)
- Edge hover shows the contract relationship (what ensures feed into what requires)
- Zoom/pan canvas
- Save/load layout
- Resizable panels

### 5.3 Visual Design Principles

- **Color coding is paramount**: green/yellow/red/gray for proof status. Use consistent, accessible colors.
- **Minimal clutter**: Show contract details on demand (click/hover), not always visible.
- **Engineer-friendly terminology**: Use "Assumes / Guarantees" instead of "requires / ensures". Use "Bit-pattern bound" and "Signed-value bound" instead of "unsigned_soundness / signed_soundness".
- **Progressive disclosure**: Overview first, details on demand.
- **Mobile-friendly**: At minimum, readable on a tablet in landscape.

### 5.4 Regeneratable from Source — Generator Script

The HTML file must NOT have contract data hardcoded. Instead, a **generator script** (preferably Python) scans the `formal/harnesses/` directory and produces the HTML automatically.

#### Workflow

```
python generate_dashboard.py
```

Running this command should:
1. Scan `formal/harnesses/<method>/` for every method folder
2. Parse each method's `.h` file for ACSL predicates (soundness predicates, helper predicates)
3. Parse each method's `.c` file for:
   - `requires` clauses
   - `ensures` clauses
   - `#ifdef FIX_*` gates (and their associated comments explaining what they fix)
   - Included `axioms_*.h` files
   - Function signature (return type, name, parameters)
4. Parse `eval_alu/eval_alu.c` to extract the dispatch edge list (which opcode calls which method)
5. Parse the existing `eval_alu_call_graph.dot` for the complete call edge list
6. Identify proof status per method:
   - If no FIX gates exist -> `proved`
   - If FIX gates exist -> `proved_with_fix`
   - If the method is `eval_alu` and the feature is usound/ssound -> `parked`
7. Generate a **single self-contained `eval_alu_contract_dashboard.html`** with all data inlined

#### Parser Requirements (Minimal Viable)

The parser does NOT need to be a full C/ACSL parser. It needs to:
- Regex-extract `@ requires` and `@ ensures` clauses (line-oriented, each clause starts on its own line)
- Regex-extract `#ifdef FIX_*` preprocessor lines
- Regex-extract function declarations (return type on its own line, then name(params))
- Regex-extract `#include "axioms_*.h"` or `"../../common/axioms_*.h"`
- Extract the structured comment above each FIX gate (the `/* ... */` block following the `#ifdef` that explains the bug)

#### Example Output Structure

The generated HTML contains a single JS object at the top of the `<script>` block:

```javascript
var CONTRACT_DATA = {
  "generated_at": "2026-07-17",
  "methods": {
    "eval_add": {
      "type": "operator",
      "status": "proved_with_fix",
      "fix_gates": [
        {
          "name": "FIX_ADD_SIGNED_32",
          "description": "For 32-bit ops the masked sums... canonicalize to sign-extended form",
          "violated_ensures": ["swidth", "ssound"]
        }
      ],
      "requires": ["msk == _32_BIT_MASK || _64_BIT_MASK", "\\valid(rd) && \\valid(rs)", ...],
      "ensures": ["type_ok", "uord", "sord", "uwidth", "swidth", "usound", "ssound"],
      "predicates": ["eval_add_unsigned_soundness", "eval_add_signed_soundness"],
      "axioms": [],
      "signature": "void eval_add(struct bpf_reg_val *rd, const struct bpf_reg_val *rs, uint64_t msk)",
      "description": "Bounds sum of two w-bit masked register values."
    },
    ...
  },
  "edges": [...],
  "levels": [
    {"id": 0, "label": "Entry Point", "methods": ["eval_alu"]},
    {"id": 1, "label": "Pre-processing", "methods": ["eval_apply_mask", "eval_fill_imm", ...]},
    ...
  ]
};
```

#### Requirements for the Generator Script

- **Standalone**: No external dependencies beyond Python 3 stdlib (`re`, `os`, `json`, `pathlib`)
- **Idempotent**: Running it twice with the same harness state produces the same output
- **Fast**: Should complete in <1 second (no heavy computation, just file scanning + regex)
- **Readable**: Well-commented Python with clear section markers
- **Resilient**: Gracefully handles missing README files, partial contracts, methods without BMC harnesses

## 6. Technical Requirements

- **Zero external dependencies** — Pure HTML/CSS/JS, runs fully offline
- **Single self-contained .html file** — Everything inline (SVG, CSS, JS)
- **Vanilla DOM + SVG APIs** — No D3, no React, no jQuery, no WebGL
- **ES5-compatible JS** — Use `var`, `function()`, no arrow functions, no template literals, no `const`/`let`, no classes
- **Canvas panning** via pointer events
- **Node drag-and-drop** with edges auto-updating
- **Save/Load layout** via JSON file download
- **Responsive** to viewport size changes

## 7. Data Model

Extract all contract data from the harness files into a JSON structure (embedded in the generated HTML):

```json
{
  "methods": {
    "eval_add": {
      "type": "operator",
      "status": "proved_with_fix",
      "fix_gates": ["FIX_ADD_SIGNED_32"],
      "requires": ["msk == _32_BIT_MASK || _64_BIT_MASK", "\\valid(rd) && \\valid(rs)", "\\separated(rd, rs)", "is_scalar", "range_ordering", "range_within_width"],
      "ensures": ["type_ok", "uord", "sord", "uwidth", "swidth", "usound", "ssound"],
      "soundness_predicates": ["eval_add_unsigned_soundness", "eval_add_signed_soundness"],
      "helper_predicates": [],
      "includes_axioms": [],
      "description": "Bounds the sum of two w-bit masked register values, handling unsigned and signed overflow via eval_umax_bound/eval_smax_bound."
    },
    ...
  },
  "edges": [
    {"source": "eval_alu", "target": "eval_add", "flow": "requires: range_ordering, range_within_width -> feeds; ensures: usound, ssound <- composes"},
    ...
  ],
  "fix_gates": { ... },
  "parked_lemmas": { ... }
}
```

## 8. Development Approach (Multi-Agent Team)

This project has a pre-configured visualization agent team in `.opencode/agents/`. Use these agents directly:

| Agent | Role | When to invoke |
|---|---|---|
| `@formal-verification-lead` | Read-only expert on verification data accuracy | Validate proof status assignments, FIX gate descriptions, contract flow correctness |
| `@tooling-engineer` | Builds the `generate_dashboard.py` generator script | When harness data extraction or the generator needs work |
| `@viz-engineer` | Builds interactive HTML/JS/SVG visualizations | When the dashboard, call graph, or CFG needs to be built or modified |
| `@tech-comms-lead` | Crafts labels, tooltips, terminology, documentation | When dashboard text needs to be engineer-friendly, or when writing prompts/docs |

### Hard Rules

- **NO modifications to files under `formal/harnesses/`** with extensions `.c`, `.h`, `*_bmc.c`, `*_main.c`, or `axioms_*.h`
- Allowed file extensions: `.html`, `.py`, `.dot`, `.md`, `.json`, `.css`, `.js`
- If you need verification data, READ the harness files — do not edit them
- If you spot an error in a proof file, report it — do not fix it

### Engineering Workflow (Skills & Commands)

This project has a structured three-phase engineering lifecycle defined as opencode skills in `.opencode/skills/`:

| Phase | Command | Skill | Purpose |
|---|---|---|---|
| **Design** | `/design <feature>` | `design-phase` | Clarify requirements, explore options, write design brief, get user approval |
| **Develop** | `/develop <brief>` | `development-phase` | Implement: Tooling Engineer + Viz Engineer in parallel, Tech Comms polish |
| **Review** | `/review` | `review-phase` | Three reviews: Technical Accuracy, UX/Clarity, Code Quality |

Each phase prompts whether to proceed to the next. Or you can run commands manually.

**For this project, the recommended flow is:**

1. Start with `/design "Build the interactive Contract Dashboard"` — this will produce a design brief
2. When approved, the flow offers to proceed to `/develop` — this coordinates the engineers
3. When implementation is done, the flow offers to proceed to `/review` — this runs all three reviews

### Invocation Examples

```
@tooling-engineer Build generate_dashboard.py that reads contract info from all 22 harnesses

@viz-engineer Implement the three-view dashboard per the design brief at formal/harnesses/design_brief_contract_dashboard.md

@tech-comms-lead Review the dashboard labels and tooltips for engineer-friendliness

@formal-verification-lead Is eval_mul PROVED or PROVED_WITH_FIX? What ensures fail without FIX_MUL_SCONST?
```

## 9. What I'm Handing You

**Project configuration (already set up):**
- `.opencode/agents/` — 4 specialized agents (formal-verification-lead, viz-engineer, tooling-engineer, tech-comms-lead)
- `.opencode/skills/` — 3 phase skills (design-phase, development-phase, review-phase)
- `.opencode/commands/` — 3 commands (`/design`, `/develop`, `/review`)
- `opencode.json` — Agent permissions, command registration, default agent settings
- `AGENTS.md` — Visualization team rules, workflow, and hard boundaries

**Existing visualizations (in `formal/harnesses/`):**
- `eval_alu_call_graph.html` — Interactive call graph (reference for drag-drop engine, force layout, save/load)
- `eval_alu_control_flow_graph.html` — Interactive control flow graph (reference for flowchart layout, edge dragging)
- `eval_alu_call_graph.dot` — Complete edge list in DOT format

**Source data:**
The full harness directory at `formal/harnesses/` with all 22+ method folders, each containing `*.c`, `*.h`, `*_bmc.c`, `*_main.c`, `README.md`, and `axioms_*.h` files.

## 10. Deliverable

The final output should include:

1. **`generate_dashboard.py`** — Python 3 script that scans `formal/harnesses/` and generates the HTML
2. **`eval_alu_contract_dashboard.html`** — Generated single self-contained HTML file that I can open in a browser and:
   - See the full call graph color-coded by verification status
   - Click any method to inspect its full contract
   - See the contract propagation chain (which requires/ensures flow between methods)
   - Explore all FIX gates and understand what they fix
   - Drag nodes, pan canvas, save/load custom layouts
   - Filter/search methods by name, status, or fix gate presence

Both files must work fully offline with zero dependencies.

Use the engineering workflow: `/design` to plan -> `/develop` to build -> `/review` to sign off.
