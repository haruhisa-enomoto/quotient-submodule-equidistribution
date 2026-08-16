# API documentation build

This nested Lake project keeps doc-gen4 outside the production dependency
graph.  From this directory:

```text
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update doc-gen4
lake build QuotientSubmoduleEquidistribution:docs
```

The generated API is written to `.lake/build/doc`.  From the repository root,
run

```text
python3 tools/serve_site.py
```

to combine it with the hand-written website and serve the complete site at
`http://localhost:8000/`.  Some doc-gen4 functionality does not work when
pages are opened as `file://` URLs.
