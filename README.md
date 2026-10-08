# KLS500

Lean 4 proofs of dimension-free bounds for every isotropic log-concave probability law $\mu$ on $\mathbb{R}^n$, $n\ge1$:

```math
\mathrm{Var}_{\mu}(f) \le 500\int \lVert\nabla f\rVert^2\,d\mu,
\qquad h(\mu) \ge \frac{100}{197\sqrt{500}}.
```

The Poincaré inequality covers locally Lipschitz $L^2$ functions. The Cheeger constant is

```math
h(\mu)=\inf_{0<\mu(A)<1}\frac{\mu^+(A)}{\min(\mu(A),1-\mu(A))},
```

where $A$ ranges over Borel subsets of $\mathbb{R}^n$ and

```math
\mu^+(A)=\liminf_{\varepsilon\downarrow0}\frac{\mu(A_\varepsilon)-\mu(A)}{\varepsilon},
```

```math
A_\varepsilon=\{x\in\mathbb{R}^n:\mathrm{dist}(x,A)\le\varepsilon\}.
```

See [Chen (2021), §1, Eq. (2) and the boundary-measure definition](https://link.springer.com/article/10.1007/s00039-021-00558-4).

The optimal **universal** Poincaré constant satisfies $4\le C_*\le500$.

| Statement | Lean declaration |
|---|---|
| Poincaré bound | `KLS500.poincare500` |
| Cheeger bound (factor 1.97) | `KLS500.cheeger197` |
| Universal range | `KLS500.universalPoincareRange` |
| Exact upstream OpenAI KLS statement | `KLS500.openaiKLS` |

Lean verification also passed for the [exact KLS conjecture statement defined by OpenAI](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/KLS/Model.lean#L51-L58), `OAI.LeanBlast.KLS.KLSStatement`, using the universal Poincaré constant 500.

The Lean development is based chiefly on the cumulant and suspension approach of [Pierre Bizeul, Boaz Klartag and Joseph Lehec](https://arxiv.org/pdf/2610.05474v1), including the tilt–spectral criterion of [Zhao Song and Xinzhi Zhang](https://arxiv.org/pdf/2610.01447v2), with quantitative refinements giving 500. The related manuscript by [Krishnakumar Balasubramanian and Shiva Kasiviswanathan](https://github.com/kriznakumar/paper/blob/4837c33649ba2271f43c9684e9350ecbdd725f95/KLS.pdf) develops a separate approach using compatible integration operators and a Hodge comparison.

See [KLS500.lean](KLS500.lean) and the separately compiled [Challenge.lean](Challenge.lean). Verification rebuilt 1,710 mathematical modules at kernel trust level zero; endpoint axiom checks found only `propext`, `Classical.choice`, and `Quot.sound`. [Evidence](verification/README.md) is included; Comparator and Nanoda were not run.

Build with Elan and the pinned dependencies:

```sh
lake exe cache get
lake build
```

Project contributions use [Apache 2.0](LICENSE); retained third-party licenses and [notices](NOTICE) apply.
