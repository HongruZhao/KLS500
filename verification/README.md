# Verification evidence

The accepted release freshly rebuilt all 1,710 mathematical modules and ran two audit modules. The endpoint closure used only Lean's standard axioms `propext`, `Classical.choice`, and `Quot.sound`. The two new public interfaces were then compiled separately without warnings; their five endpoint axiom closures were checked again.

`verification-summary.json` and `final-verification-receipt.json` describe the accepted full build. `public-interface/` records the later interface checks. `portable-source-inventory.json` uses the original release prefix `lean/`; remove that prefix to locate these unchanged sources at this repository's root. Existing receipts retain original execution paths and historical package/report hashes. The report is being revised separately and is not part of this code upload.

The root Lake configuration preserves all accepted source targets and dependency pins, adding two separate public-interface targets. Packaging checks are in `github-package-check.json`. Source inventories and logs are evidence of these runs, not a claim that this new checkout received another complete rebuild. Cached compiled objects are not distributed. Comparator and Nanoda have not been run. Review is self-assessed with agent assistance; no independent human semantic review is claimed.
