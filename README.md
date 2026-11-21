# Rank-unimodality of one-descent composition ideals

**Zhang Yibo** · [ORCID 0009-0002-2005-5781](https://orcid.org/0009-0002-2005-5781)  
**Zhang Zhanhe** · [ORCID 0009-0007-2883-9640](https://orcid.org/0009-0007-2883-9640)

Both authors contributed equally as joint first authors. Zhang Zhanhe is the corresponding author.

Preprint v1.0.2 · 21 November 2026

For a composition $w$, consider the distinct words obtained by deleting parts and decreasing the surviving parts to positive integers. Count each word once and rank it by its total weight. If the part sizes of $w$ have at most one adjacent descent, these counts form a unimodal sequence. The same holds for every bitonic composition, whose parts first weakly increase and then weakly decrease. There is no restriction on the lengths or part sizes.

The proof couples the weight, length and unused weight of a subword of a monotone composition at successive budgets. This gives a coefficient inequality at every deletion prefix of an arm. A strict-peak induction turns that inequality into unimodality of the original rank coefficients. The result settles the one-descent case of Conjecture 2.6 in Vatter's *An assortment of problems in permutation patterns*. [Conjecture and context](https://arxiv.org/abs/2602.16355)

## Paper and proofs

| Document | Contents | Source |
| --- | --- | --- |
| [Main paper](paper/one_descent_rank_unimodality.pdf) | Theorem 1.1, the monotone-host coupling and the single-arm coefficient inequality (6 pages). | [LaTeX](paper/one_descent_rank_unimodality.tex) |
| [The hereditary strict-peak reduction](paper/strict_peak_reduction.pdf) | The two inductions, the finite certificate and the joins at a strict peak (5 pages). | [LaTeX](paper/strict_peak_reduction.tex) |
| [Detailed coefficient lemmas](paper/detailed_coefficient_lemmas.pdf) | The estimates and auxiliary lemmas used in the reduction (31 pages). | [LaTeX](paper/detailed_coefficient_lemmas.tex) |

The complete proof sources, the earlier foundation of the induction, the exhaustive certificate and its replay scripts are in the full archive **OneDescent-Full-v1.0.2.zip**. Its SHA-256 is recorded in [RELEASE_SHA256.txt](RELEASE_SHA256.txt).

## Reproducing the result

From this repository's root, run the following command using standard-library Python 3.10 or later.

    python verify.py

It checks the file inventory and reproduces three exact calculations. These cover 9,081 arm instances, all 6,095 distinct qualifying hosts through weight 14, and 21,280 strict-peak boundary instances. The literal calculation enumerates distinct words directly. The boundary calculation covers heavier-arm weight below, equal to, and above the peak.

For the exhaustive part of the proof, extract the full archive and run the following command from the directory containing its README.txt.

    python verify_evidence.py --replay

This also reconstructs the 1,858,242 owner/rank inputs in the finite branch of the mixed case, including its 72,043 positive-curvature inputs. The mathematical reduction to that finite domain is given in the strict-peak companion and the associated source proofs.

In [DepthSlackTransport.lean](formal/DepthSlackTransport.lean) and [DepthSlackArmIdentities.lean](formal/DepthSlackArmIdentities.lean), Lean checks 19 transport and ratio statements and seven polynomial identities, respectively. The interpretation for distinct words and the full strict-peak induction are proved in the articles. Given a built Mathlib checkout at the revision recorded in [environment.json](formal/environment.json), run the following command inside the extracted full archive, replacing the last argument with the path to that checkout.

    python verify_evidence.py --mathlib-project PATH_TO_MATHLIB_PROJECT

The [verification report](verification_report.json) gives the scope and counts of the final review. The file digests in [SHA256SUMS.txt](SHA256SUMS.txt) cover the mathematical material, verification scripts and release checksum. The author order, ORCID identifiers and preferred citation for the preprint are recorded in [CITATION.cff](CITATION.cff).
