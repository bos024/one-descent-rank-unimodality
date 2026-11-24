# Rank-unimodality of one-descent composition ideals

**Zhang Yibo** · [ORCID 0009-0002-2005-5781](https://orcid.org/0009-0002-2005-5781)  
**Zhang Zhanhe** · [ORCID 0009-0007-2883-9640](https://orcid.org/0009-0007-2883-9640)

Both authors contributed equally as joint first authors. Zhang Zhanhe is the corresponding author.

Preprint v1.0.2 · 21 November 2026 · [arXiv:2611.28619v1](https://arxiv.org/abs/2611.28619v1)

The initial public archive of the manuscripts and short checks is available on Zenodo at [10.5281/zenodo.24420830](https://doi.org/10.5281/zenodo.24420830).

For a composition $w$, consider the distinct words obtained by deleting parts and decreasing the surviving parts to positive integers. Count each word once and rank it by its total weight. If the part sizes of $w$ have at most one adjacent descent, these counts form a unimodal sequence. The same holds for every bitonic composition, whose parts first weakly increase and then weakly decrease. There is no restriction on the lengths or part sizes.

The proof couples the weight, length and unused weight of a subword of a monotone composition at successive budgets. This gives a coefficient inequality at every deletion prefix of an arm. A strict-peak induction turns that inequality into unimodality of the original rank coefficients. The result settles the one-descent case of Conjecture 2.6 in Vatter's *An assortment of problems in permutation patterns*. [Conjecture and context](https://arxiv.org/abs/2602.16355)

## Paper and proofs

| Document | Contents | Source |
| --- | --- | --- |
| [Main paper](paper/one_descent_rank_unimodality.pdf) | Theorem 1.1, the monotone-host coupling and the single-arm coefficient inequality (6 pages). | [LaTeX](paper/one_descent_rank_unimodality.tex) |
| [The hereditary strict-peak reduction](paper/strict_peak_reduction.pdf) | The two inductions, the finite certificate and the joins at a strict peak (5 pages). | [LaTeX](paper/strict_peak_reduction.tex) |
| [Detailed coefficient lemmas](paper/detailed_coefficient_lemmas.pdf) | The estimates and auxiliary lemmas used in the reduction (31 pages). | [LaTeX](paper/detailed_coefficient_lemmas.tex) |

The complete v1.0.2 proof supplement is available in [reproducibility/](reproducibility/). It includes the written dependencies, the exact finite certificate, its generators and the independent replay code. [RELEASE_SHA256.txt](RELEASE_SHA256.txt) records the digest of the original ZIP from which these files were extracted.

## Reproducing the result

Run these commands from the repository root using standard-library Python 3.10 or later.

```sh
python verify.py
python reproducibility/verify_evidence.py --replay
```

The first command checks the original public files and runs three short audits. The second checks the complete evidence inventory and reruns six calculations in temporary working directories. It independently reconstructs all 1,858,242 admissible inputs to the finite branch of the proof, including the 72,043 positive-curvature inputs. The supplied replay checks the digests of the historical binary checkpoints without deserializing them.

The [finite certificate generator](reproducibility/reduction/build_first_missing_twelve_head_certificate.py), [independent enumerator](reproducibility/reduction/verify_first_missing_twelve_head_certificate.py), [certificate data](reproducibility/reduction/first_missing_twelve_head_certificate_data.json) and [compressed stream of critical rows](reproducibility/reduction/first_missing_twelve_critical_rows.jsonl.gz) are included with their dependencies. The two-seed calculations are documented in the [two-seed audit](reproducibility/reduction/audit_binary_CI_tail_and_two_seeds.py) and its [archived results](reproducibility/reduction/audit_binary_CI_tail_and_two_seeds.json). See the [proof index](reproducibility/checks/coefficient_proof_index.json) and the [supplement guide](reproducibility/README.txt) for the links between calculations and proofs.

### Lean project

With Git and [Elan](https://lean-lang.org/install/) installed, run the following commands from the repository root. [lean-toolchain](lean-toolchain) selects Lean 4.34.0, and [lake-manifest.json](lake-manifest.json) pins Mathlib and its dependencies. The first command downloads precompiled Mathlib dependencies and may take a few minutes.

```sh
lake exe cache get
python reproducibility/verify_evidence.py --mathlib-project .
lake env python reproducibility/check_lean_certificates.py
```

The second command checks the evidence inventory and type-checks 19 transport and ratio statements and seven polynomial identities in the two main Lean modules. The third command type-checks the finite arithmetic certificate and the associated estimates one module at a time. Allow several minutes for that command. The Lake targets `PaperProofs` and `FiniteCertificates` also expose these modules to the Lean editor. The correspondence with distinct subwords and the full strict-peak induction are proved in the manuscript and appendices.

The [verification report](verification_report.json) records the scope of the manuscript checks. Author and citation information is in [CITATION.cff](CITATION.cff), and permissions are set out in [LICENSE](LICENSE).

For a reproducible citation of the complete certificate, use a link to a specific commit of this repository. The Zenodo link above identifies the initial public archive.
