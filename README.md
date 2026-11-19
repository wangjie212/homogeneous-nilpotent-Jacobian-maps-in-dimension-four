# Dimension-four homogeneous dependence in Lean

This project formalizes Jie Wang and Dan Yan’s *Linear dependence and tameness for homogeneous nilpotent-Jacobian maps in dimension four*. Import `DimensionFourDependence` to use the results.

## Main results

| Result | Checked statement |
| --- | --- |
| Theorem 1.1 | Positive-degree homogeneous maps in four variables with nilpotent Jacobian have linearly dependent components over any characteristic-zero field. [`theorem_1_1`](DimensionFourDependence/HomogeneousDependenceTheorem.lean#L47) |
| Theorem 1.2 | The map `X + H` is a polynomial automorphism and is tame after adjoining one variable in every positive degree. Ordinary tameness holds through degree five and in the independent ternary branch. [`theorem_1_2`](DimensionFourDependence/OriginalFieldTernaryClassification.lean#L71) |
| Theorem 6.1 | The classification of three-variable maps with nilpotent Jacobian and zero constant term holds over the original characteristic-zero field. [`theorem_6_1`](DimensionFourDependence/OriginalFieldTernaryClassification.lean#L51) |

The development covers the paper’s numbered auxiliary results and both examples in Section 5.6. [Lemma 4.4](DimensionFourDependence/Lemma44.lean#L35) uses specialization of projective Hilbert functions to prove the degree bound. [Corollary 5.3](DimensionFourDependence/Corollary53OriginalCoordinates.lean#L47) classifies the geometric generic fiber components as lines or plane conics and proves the component-count divisibility using the free action of roots of unity. The examples give a [generic parabola in characteristic zero](DimensionFourDependence/PlaneConicExampleFiber.lean#L44) and [independent components in positive characteristic](DimensionFourDependence/PositiveCharacteristicExample.lean#L86).

## Build and verify

The project pins Lean 4.34.0 and Mathlib v4.34.0. With Lean installed through Elan, run these commands from the project directory.

```sh
lake update
lake build
lake env lean validation/axioms.lean
```

On the original Windows workstation, the local scripts reuse the existing Mathlib cache and regenerate the audit.

```sh
python scripts/check.py --timeout 600
python scripts/audit.py
```

Both scripts accept `--lean-bin` and `--packages` to override the local paths.

The [recorded audit](validation/audit.json) covers **5,948 theorems and 7,196 declarations** across 2,006 compilation targets, with zero admitted proofs and zero custom axioms.
