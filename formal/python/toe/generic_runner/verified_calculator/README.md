# Verified Physics Calculator v1

This package is the trusted, domain-neutral calculator core. It does not import
historical runners, candidate generators, or scientific acceptance/oracle code.

The trust boundary is intentionally asymmetric:

```text
AI / human / historical runner / unsafe plugin
                    |
                    v
             CandidatePacketV1
                    |
================ verifier boundary ================
                    |
         Python exact DAG recomputation
              /             \
      Julia/Nemo route    Lean runtime certificate
              \             /
          per-output challenge coverage
                    |
             computational receipt
                    |
        separate authority attachment
```

No calculation changes scientific authority. `VERIFIED_EXACT` is issued per
output only when Python, Julia, Lean, and every applicable mandatory challenge
are bound to the same computation. Floating solver agreement is always
`CROSSCHECKED_NUMERICAL`; only a checked containment certificate can become
`VERIFIED_ENCLOSURE`.

The public module is `formal.python.toe.generic_runner.verified_calculator`.
The equivalent CLI is:

```powershell
python -m formal.python.toe.generic_runner.verified_calculator --help
```

`plugin-run --unsafe-allow-arbitrary-code` is developer-only and is not an OS
sandbox. Its output is always an untrusted candidate.

The frozen C03/RV policy census intentionally says that its exact milestone is
not yet earned. The historical 16-root graph must first be lowered into this
package's declarative IR and independently reimplemented in Julia.
