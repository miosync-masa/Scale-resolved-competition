# NSBarrier

NSBarrier is a Lean 4 formalization of the theorem chain behind the NSBarrier project.
It is organized as a proof-oriented library rather than a single monolithic script: abstract barrier arguments, finite-dimensional Galerkin realization, shell geometry, Fourier and Bernstein estimates, PDE-facing regularity interfaces, compactness and limit bridges, and paper-facing master theorems are split across the `NSBarrier/` directory.

This directory is intended to live as a subdirectory inside a larger repository. The top-level files in this folder provide convenient import surfaces for two different use cases.

## Import surfaces

`NSBarrier.lean` is the public surface.
It imports the paper-facing chain and the main bridge files that are useful when reading or citing the project at a high level. If you want the core theorem surface without loading every internal implementation file, use:

```lean
import NSBarrier
```

`NSBarrier/All.lean` is the exhaustive surface.
It imports the full internal library, including lower-level construction files, implementation details, and bridge modules used to assemble the complete development. If you want a one-shot import of the entire local library, use:

```lean
import NSBarrier.All
```

In short:

- `import NSBarrier` for the curated public theorem surface.
- `import NSBarrier.All` for the complete internal development.

## Repository layout

The codebase is centered in the `NSBarrier/` directory.
The module structure follows the theorem pipeline used in the project:

- Abstract barrier and finite-source core.
- Integrated and Galerkin shell identities.
- ODE realization and finite-dimensional existence.
- Triad geometry and shell locality.
- Finite-band Fourier and Bernstein input.
- Shell-block, modewise, and localized production estimates.
- PDE-facing regularity and projected Navier-Stokes interfaces.
- Bootstrap, continuation, no-blowup, uniform-in-`K_max`, compactness, and limit bridges.
- Paper-facing master theorems and frontier files.

Two documentation files are especially useful when navigating the library:

- `NSBarrier/THEOREM_MAP_ANNOTATED.md`
- `NSBarrier/FULL_THEOREM_REGISTRY.md`

The theorem map gives a layered guide to the development.
The full registry lists the declarations intended for appendix and audit work.

## Typical workflow

For theorem-surface work, start from:

```lean
import NSBarrier
```

For maintenance, registry generation, or whole-project inspection, start from:

```lean
import NSBarrier.All
```

If your editor reports no messages after loading `NSBarrier/All.lean`, the full import surface is resolving cleanly across the local library.

## Notes

This project is intentionally split into many small modules.
That granularity is deliberate: it keeps the proof chain auditable, makes paper-facing dependencies easier to track, and helps isolate bridge files from foundational files without collapsing the entire development into a single import target.
