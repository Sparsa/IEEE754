# Graph Report - .  (2026-06-04)

## Corpus Check
- Corpus is ~3,561 words - fits in a single context window. You may not need a graph.

## Summary
- 34 nodes · 26 edges · 9 communities (6 shown, 3 thin omitted)
- Extraction: 100% EXTRACTED · 0% INFERRED · 0% AMBIGUOUS
- Token cost: 1,000 input · 500 output

## Community Hubs (Navigation)
- [[_COMMUNITY_IEEE 754 Formal Verification|IEEE 754 Formal Verification]]
- [[_COMMUNITY_Lake Manifest Config|Lake Manifest Config]]
- [[_COMMUNITY_OpenCode Plugin Infrastructure|OpenCode Plugin Infrastructure]]
- [[_COMMUNITY_OpenCode Schema Config|OpenCode Schema Config]]
- [[_COMMUNITY_Plugin Dependencies|Plugin Dependencies]]
- [[_COMMUNITY_Decode-Encode Pipeline|Decode-Encode Pipeline]]

## God Nodes (most connected - your core abstractions)
1. `IEEE 754-2019 Formal Verification` - 9 edges
2. `Graphify OpenCode Plugin` - 3 edges
3. `@opencode-ai/plugin API` - 2 edges
4. `Knowledge Graph CLI Reminder` - 2 edges
5. `decode-exactOp-round-encode Pipeline` - 2 edges
6. `packagesDir` - 1 edges
7. `packages` - 1 edges
8. `lakeDir` - 1 edges
9. `fixedToolchain` - 1 edges
10. `$schema` - 1 edges

## Surprising Connections (you probably didn't know these)
- `OpenCode Configuration` --references--> `Graphify OpenCode Plugin`  [EXTRACTED]
  .opencode/opencode.json → .opencode/plugins/graphify.js
- `@opencode-ai/plugin API` --implements--> `Graphify OpenCode Plugin`  [EXTRACTED]
  .opencode/package.json → .opencode/plugins/graphify.js

## Import Cycles
- None detected.

## Communities (9 total, 3 thin omitted)

### Community 0 - "IEEE 754 Formal Verification"
Cohesion: 0.22
Nodes (9): Remaining Proof Gaps (F64), DecodedFloat, F32 (BitVec 32), F64 (BitVec 64), fadd_posZero_r proof (completed), flt_trans proof (completed), Hardware Oracle Interface (Python/ctypes), IEEE 754-2019 Formal Verification (+1 more)

### Community 1 - "Lake Manifest Config"
Cohesion: 0.29
Nodes (6): fixedToolchain, lakeDir, name, packages, packagesDir, version

### Community 2 - "OpenCode Plugin Infrastructure"
Cohesion: 0.33
Nodes (6): Bash Tool Execution Hook, Graphify OpenCode Plugin, Knowledge Graph CLI Reminder, OpenCode Configuration, @opencode-ai/plugin API, Package Dependencies

## Knowledge Gaps
- **21 isolated node(s):** `version`, `packagesDir`, `packages`, `name`, `lakeDir` (+16 more)
  These have ≤1 connection - possible missing edges or undocumented components.
- **3 thin communities (<3 nodes) omitted from report** — run `graphify query` to explore isolated nodes.

## Suggested Questions
_Questions this graph is uniquely positioned to answer:_

- **Why does `IEEE 754-2019 Formal Verification` connect `IEEE 754 Formal Verification` to `Decode-Encode Pipeline`?**
  _High betweenness centrality (0.083) - this node is a cross-community bridge._
- **Why does `decode-exactOp-round-encode Pipeline` connect `Decode-Encode Pipeline` to `IEEE 754 Formal Verification`?**
  _High betweenness centrality (0.017) - this node is a cross-community bridge._
- **What connects `version`, `packagesDir`, `packages` to the rest of the system?**
  _21 weakly-connected nodes found - possible documentation gaps or missing edges._