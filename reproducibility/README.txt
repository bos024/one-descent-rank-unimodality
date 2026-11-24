Rank-unimodality of one-descent composition ideals
Preprint v1.0.2 | 21 November 2026

Zhang Yibo  |  https://orcid.org/0009-0002-2005-5781
Zhang Zhanhe  |  https://orcid.org/0009-0007-2883-9640
Both authors contributed equally as joint first authors. Zhang Zhanhe is the corresponding author.
Citation metadata are in CITATION.cff.

Theorem
For every composition with at most one adjacent descent, the numbers of distinct dominated compositions of each total weight form a unimodal sequence. The same conclusion holds for bitonic compositions. The peak, all part sizes, the number of parts and the total weight are arbitrary.

Reading order
1. one_descent_rank_unimodality.pdf (6 pages). Theorem 2.1 couples completed weight, length and unused weight as the total budget increases. Theorem 3.1 and Corollary 3.2 compare a positive coefficient difference and an earlier cumulative coefficient of a single genuine arm. Theorem 1.1 gives unimodality of the original rank coefficients.
2. strict_peak_reduction.pdf (5 pages). The companion gives the product and peak inductions and their boundary cases. On the initial range n<M the reversed window difference is p_n. This also settles the case where the heavier arm has weight equal to or below the peak.
3. detailed_coefficient_lemmas.pdf (31 pages). The longer appendix gives the mathematical estimates underlying the reduction. Its selected historical proofs are indexed in checks/coefficient_proof_index.json. Each of the three papers has a self-contained TeX source with the same basename as its PDF.

Exact reproduction
Extract the entire archive. From the directory containing this file, run the following commands with standard-library Python 3.10 or later.

    python verify_evidence.py
    python verify_evidence.py --replay

The first command checks the listed file digests, 1,850 references between archived records and the printed Lean theorem reports. The second repeats six checks in temporary working directories. It enumerates actual single-arm coefficients and literal principal ideals, reconstructs the finite certificate at first missing weights ten through twelve, repeats the mixed-source and hereditary coefficient checks, and checks the two initial ranges of the strict-peak proof. Run with assertions enabled (the default).

The finite certificate is a proof premise. Analytic bounds give 3,241 rank states. Their 399 complementary states yield 1,858,242 admissible owner/rank inputs. All 72,043 positive-curvature inputs satisfy the required integer inequality. The independent reconstruction checks these inputs, the associated source operands, and the scalar certificate expressions. See reduction/first_missing_twelve_original_criterion_proof.tex for the reduction and reduction/verify_first_missing_twelve_head_certificate.py for the enumeration.

The literal word-set calculation checks all 6,095 one-descent or bitonic hosts through total weight 14. These classes overlap. Other validation includes 9,081 monotone arms and 21,280 strict-peak instances in the boundary calculation. These are consistency checks on the combinatorial model.

Formal verification
DepthSlackArmIdentities.lean verifies seven polynomial identities for arbitrary finite capacity lists. DepthSlackTransport.lean verifies nineteen transport, induction and ratio statements over arbitrary budgets. The correspondence between actual word distributions and the algebra, the Toeplitz comparisons and the strict-peak assembly are proved in writing. Earlier finite certificates carry their own Lean records.

With a built Mathlib project of the version in checks/formal_environment.json, run the following command, replacing the last argument with its directory.

    python verify_evidence.py --mathlib-project PATH_TO_MATHLIB_PROJECT

If lean is on PATH and Mathlib is on LEAN_PATH, use python verify_evidence.py --lean. The tested toolchain is Lean 4.34.0. Each of the three LaTeX articles can be compiled separately with Tectonic or a LaTeX distribution providing the packages listed in its source.

Provenance
The current results are in the three PDFs at the top level. The foundations/ and reduction/ directories preserve earlier mathematical work used by the proof, including dated statements of what was open at the time. The publication copy replaces machine-specific directory settings with local paths and refreshes their file digests. The Lean sources, numerical tables for the finite certificate, its compressed stream of critical rows, and the stored binary computation states are preserved. The replay checks the historical binary checkpoints by digest and does not deserialize them. See verification_report.json for the review scope and results.
