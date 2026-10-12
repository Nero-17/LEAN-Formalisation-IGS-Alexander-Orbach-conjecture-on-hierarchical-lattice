# Independent semantic review

Research mode: Standard Research. Agent 3, `density_audit`; review began 2026-10-12 07:33:36 UTC. Critical review target/requested effort: max; effective setting unverified. This file records semantic review; the final disposition is supplied separately only after the frozen closure gate succeeds.

The reviewed manuscript is commit `bfb73c0c34450dbb517261655cddda005b870d95`, raw Git-blob SHA256 `cc53804aafbe60b25a644b829285ac558447ccafed538408a76f736fbf3efa60`. I read the raw change from `551b8a5` independently. It changes introductory references/prose, the density discussion, and bibliography presentation; the mathematical argument under review is unchanged. Agent 1's independently prepared correspondence records 114 unchanged mathematical statement/proof environments and 74 inherited obligations. External accuracy of the new literature-summary prose and the separate Chinese companion are outside this Lean audit.

## Material claims and findings

| Claim ID | Semantic disposition | Finding |
|---|---|---|
| LATEST-NORMALIZATION | ACCEPT | Actual statewise vertex limits have expectation equal to the right Perron coordinates; the left/right pairing is one. The connected population and vertex limits use the same random variable. The saved-history index shift is explicitly `n + 1`, and the final result includes L2 convergence. |
| LATEST-CLOCKS | ACCEPT | The normalized count ratios use the same actual connected mass on the innovation probability space. The edge clock coefficient is `1 / (2 * v.connected * mass)` and vertex coefficient `1 / mass`. Full path construction is inherited; the new result is a clock-coefficient adapter. |
| DENS-FAMILY | ACCEPT | The appendix network is an actual finite simple classical rule. Source incidence has exactly the two displayed edges; graph degree transport proves both terminal degrees two. Single-edge deletion and the source incident cut prove mincut two. Terminal distance is two. |
| DENS-CRITICAL | ACCEPT | The probability is the rule's own interior reliability fixed point, with the actual reliability formula. The finite prefix uses `max length 2`, so every chosen sequence term remains classical. |
| DENS-BINOMIAL | ACCEPT | Actual path-status laws and crossing conditioning supply the success-count and reciprocal estimates. No independent binomial model is substituted for the graph law. |
| DENS-BLOCK-MOMENTS | ACCEPT | The actual electrical response is transferred to the typed circuit response before applying finite-product Laplace, path, block, and long-branch estimates. |
| DENS-WHOLE-MOMENTS | ACCEPT | The exact split is the short-open event and short-closed/long-open event. Their critical coefficients yield the mean lower bound and second-moment upper bound. Short/long independence is used before whole-rule-crossing conditioning; no false conditional independence is assumed. |
| DENS-GENERATION | ACCEPT | The eventual cutoff is quantified before every finite positive mean-one input law of variance at most eight. Every actual finite recursive generation is one such law. Homogeneity and induction supply finite-scale lower bounds, which are transferred to the same natural completion. |
| DENS-UPPER | ACCEPT | Unit input is instantiated using `Unit`; its weighted cell mean is proved equal to the actual conditional mean resistance. The existing natural-completion comparison supplies the upper bound, with no electrical estimate as an input. |
| DENS-FULL-MASS | ACCEPT | The full three-state mass matrix, including retained dangling parts and closed frontier cells, gives the stated strict lower and upper mass estimates. Both inherited sides of a `both` child come from the same failed configuration and count as one child. |
| DENS-LIMIT | ACCEPT | The final numerical theorem has only the interval endpoints and `1 ≤ lower`, `upper ≤ 2`, `lower < upper` as premises. It applies the proved lower and upper resistance bounds to `appendixNaturalCompletion`, obtains the spectral limit, and chooses a finite family index. No moment, transform, resistance bound, or desired density assertion is a final premise. |
| DENS-PHYSICAL | ACCEPT | The final physical theorem uses exactly the numerical theorem's rule, own critical probability, and `appendixNaturalCompletion`. Its predicate includes actual physical vertex-limit mass, compact electrical space, spectral data, and the physical-mass-almost-everywhere heat-kernel small-time limit on an almost-sure environment event. The four terminal parameters equal two in the same existential witness. |

All material claim IDs above follow the correspondence ledger, rather than inventing new IDs for the same claims. Their proof status is PROVED once the independently frozen compilation/axiom gate passes; until then this file is static semantic acceptance only.

## Scope and strongest remaining objection

The finite-input invariant is precisely the version needed by every finite graph generation. No separately exported theorem for arbitrary nonfinite input probability laws is claimed. The exported normalized variance bound is at most eight; the proof's internal strict estimate must not be described as a literal exported strict bound. The formal limiting logarithmic rate suffices for density; not every auxiliary prose `O(1)` statement is exported verbatim. Allowing real `base > 1` in Lean gives the same finite graph construction and suffices for the finite-rule theorem, although the paper elects to choose rational bases.

The physical conclusion is the compact diffusion's small-time exponent at physical-mass-typical points. It does not assert every-born-vertex, arbitrary-ball exit-time, or microscopic infinite-graph long-time exponents. Density near four thirds does not give exact equality for a finite rule and does not settle global Alexander--Orbach exclusion.

Before the final gate, the strongest remaining objection is artifact freshness: semantic inspection and historical successful receipts alone are not the final complete closure certificate. The decisive next check is the running frozen source/object/imported-constant gate. It includes all imported local modules and vendored Universality modules; previous root public-theorem transitive axiom checks already covered reachable vendor axioms, while this gate additionally enumerates every imported vendor-owned constant.

## Verification routes and evidence limits

Historical root and vendor source/object hashes are reused only when exact bytes and toolchain/dependency-lock fingerprints match. The vendor upstream source manifest is authenticated by its verification record, and the installed compiler SHA256 matches that record. Its historical allowance for unrelated external axioms is not adopted. The final imported closure permits only `propext`, `Classical.choice`, and `Quot.sound`.

Successful standalone compilation receipts for 67 current modules are normalized as compilation evidence. Those old per-module receipts did not record direct dependency fingerprints; this limitation is retained in the seed metadata. Current full dependency hashes, fresh compilation of the four repaired/final interfaces and the aggregate, and exhaustive final transitive axiom enumeration are the acceptance evidence. A fresh source rebuild or fresh kernel-body recheck of every cached declaration is not claimed.

An additional optional direct `Kernel.check` probe was attempted, but its error formatter failed to elaborate because `Kernel.Exception` had no `ToMessageData` instance. It provides no proof evidence. It was abandoned without changing Lean sources; the established source-compilation and axiom-audit route remains the gate.

No manuscript, Lean source, Git state, or Drive file was edited by this reviewer. Generated compiler objects, receipts, verifier scripts and review reports were written. Publication and archive success require their own receipts and are not inferred from this semantic review.
