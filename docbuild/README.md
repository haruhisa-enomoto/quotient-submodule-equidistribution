# API documentation build

This nested Lake project keeps doc-gen4 outside the production dependency
graph.  From this directory:

```text
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update doc-gen4
lake build OpConjecture:docs
```

The generated site is written to `.lake/build/doc`.  Serve it over HTTP; some
doc-gen4 functionality does not work when pages are opened as `file://` URLs.

