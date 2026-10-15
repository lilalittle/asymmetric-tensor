# asymmetric-tensor

Lean 4 formalization of the asymmetric metric-tensor and the thermodynamic
equation of state, by Binyamin Tsadik Bair-Mosheh.

The formalization itself is under review in PR #1. This branch holds the
project skeleton.

## Building

Requires [elan](https://elan.lean-lang.org):

```
lake update
lake exe cache get
lake build
```

## License

Apache-2.0 — the `LICENSE` file arrives with the code contribution (PR #1).
