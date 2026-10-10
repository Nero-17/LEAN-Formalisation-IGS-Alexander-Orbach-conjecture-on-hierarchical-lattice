# External proof provenance

The finite-dimensional fixed-point foundation is adapted from
[harfe/fixed-point-theorems-lean4](https://github.com/harfe/fixed-point-theorems-lean4/tree/770940ddf9878cf61952ed53d910b92bca841838),
commit `770940ddf9878cf61952ed53d910b92bca841838` (MIT).
The complete copyright and permission notice is in `Harfe-MIT.txt`.
Original source byte hashes are in `Brouwer-source-manifest.json`.

Five complete source modules are imported: cubical Sperner preparations,
cubical Sperner, the fixed point on the unit cube, convex-set homeomorphisms,
and Brouwer. The actual upstream toolchain was 4.32.0; its README named an
older release. This project recompiles sources under Lean 4.32.1 and the pinned
mathlib; upstream compiled objects are not used.

The import script changes local imports, encloses all declarations in
`IGSIII34.Topology.Vendor`, and replaces the aggregate `Mathlib.Tactic` import
with the individual tactic modules. It preserves the original mathematical
statements and proof bodies. Any later proof compatibility changes must be
recorded here. Verification status is controlled by the complete project
manifest and transitive axiom log, not merely by this source notice.

The external source proves the finite-dimensional Brouwer theorem. Local modules
`IGSIII34.Topology.Schauder` and `IGSIII34.Probability.ConvexLaws` separately
prove the locally convex and actual probability-law versions of Schauder from it.
The electrical map's compact moment domain, invariant bounds and continuity
remain separate, unfinished obligations.
The external foundation's declarations are not new research results.
