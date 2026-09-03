# Lean certificate: algebraic core of the `sqrt 6` kissing-number bound

This Lean 4 / Mathlib project checks the numerical estimates, the two-step cap-fraction induction, the cancellation of a positive cap fraction, the exceptional dimension-three calculation, and the optimality forced by dimension two.

## Exact scope

The standard geometric facts that a kissing configuration determines spherical caps of angular radius `pi/6` with disjoint interiors, and that their normalized surface area is

`(integral 0..pi/6 sin(t)^(n-2) dt) / (integral 0..pi sin(t)^(n-2) dt)`

are not yet formalized here. They enter only through explicit packing hypotheses in the final Lean declarations; no project axiom is introduced.

## Reproduce

```bash
lake build
bash scripts/check.sh
```

The project pins Lean `v4.33.1` and Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`.
