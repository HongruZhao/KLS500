# KLS500

Lean 4 proofs of dimension-free bounds for every isotropic log-concave probability law $\mu$ on $\mathbb R^n$, $n\ge1$:

$$\operatorname{Var}_\mu(f)\le500\int\|\nabla f\|^2\,d\mu,\qquad h(\mu)\ge\frac{100}{197\sqrt{500}}.$$

The Poincaré inequality covers locally Lipschitz $L^2$ functions. The Cheeger constant uses closed Euclidean neighborhoods and denominator $\min\{\mu(A),1-\mu(A)\}$. The optimal **universal** Poincaré constant satisfies $4\le C_*\le500$.

| Statement | Lean declaration |
|---|---|
| Poincaré bound | `KLS500.poincare500` |
| Cheeger bound (factor 1.97) | `KLS500.cheeger197` |
| Universal range | `KLS500.universalPoincareRange` |
| Exact upstream OpenAI KLS statement | `KLS500.openaiKLS` |

See [KLS500.lean](KLS500.lean) and the separately compiled [Challenge.lean](Challenge.lean). The proof follows the Bizeul–Klartag–Lehec route with quantitative refinements. Verification rebuilt 1,710 mathematical modules at kernel trust level zero; endpoint axiom checks found only `propext`, `Classical.choice`, and `Quot.sound`. [Evidence](verification/README.md) is included; Comparator and Nanoda were not run.

Build with Elan and the pinned dependencies:

```sh
lake exe cache get
lake build
```

Project contributions use [Apache 2.0](LICENSE); retained third-party licenses and [notices](NOTICE) apply.
