# HOL4 metatheory rules

Files here are proof sources, not documentation substitutes.

- Keep definitions close to the published λΠ-calculus-modulo rules.
- Prefer existing HOL4 relation/lambda infrastructure where it exactly matches.
- Every admitted assumption must appear as a theorem premise or an explicit
  locale-style predicate; do not hide it in automation.
- TacticToe/HOLyHammer/Metis may discover proofs, but final scripts must replay
  through HOL4.
- The target subset matches Kontroli: first-order rewrite patterns, annotated
  rewrite variables where required, and optional eta convertibility.
- Add implementation correspondence only after the declarative metatheory is
  independently buildable.
