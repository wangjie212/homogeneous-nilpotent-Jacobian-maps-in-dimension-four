"""Compile the proof project using the installed Lean and cached Mathlib.

No theorem files from the neighboring project are placed on LEAN_PATH.
The cache is used read-only. On other machines, `lake build` is the normal route.
"""
import argparse
import hashlib
import json
import os
import re
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
MODULES = [
    "Defs", "Homogeneous", "Basic", "LinearSubst", "Nilpotent", "Flag",
    "NilpotentKernel", "NilpotentFlag", "NilpotentCubicFlag", "ConstantField", "AlgebraicDerivation", "AlgebraicDifferential",
    "RationalDerivative", "RationalPartial", "AlgebraicPartial", "OutputCoordinates",
    "CoefficientField", "AmbientDerivation", "CoefficientChainRule", "QuadraticDifferentiation", "CubicDifferentiation", "FiberPolynomialForms", "FiberPolynomialGradients", "SourceTranscendence",
    "VerticalDerivation", "FiberJacobian", "JacobianRank", "OutputSelection", "FirstInvariant",
    "FirstInvariantChart", "SecondInvariant", "ThirdCovector", "ThirdInvariant", "FiberEquations", "FiberEquationSystem", "AffineHyperplane", "FiberCommonFactors", "FiberCoprimeEquations", "MultivariateHomogenize", "HomogenizeChart", "HomogenizeCoprime", "ProjectiveFiberEquations", "CoefficientCurveField", "FiberCoordinateField", "FiberCoordinateRing", "FiberPrimeDimension", "FiberPrimeHeight", "Laplacian", "Shear",
    "ProjectiveCone", "ProjectiveFiberPrime", "ProjectiveComponents", "CompleteIntersectionPair", "ProjectiveHilbert", "HomogeneousIntersection", "SmallIntersectionHilbert", "HilbertCoordinateRecurrence", "DiscreteHilbertPolynomial", "HilbertPolynomialExistence", "HilbertPolynomialBounds", "FiberHilbertLowerBound", "FiberHilbertDegree", "ScalarExtensionRank", "HomogeneousBaseChange", "HilbertFieldExtension", "GeometricHilbertBound", "FiberAlgebraicBaseChange", "FiberComponentContraction", "ComponentGenericPoint", "ConeFieldExtension", "GeometricFiberComponents", "ProjectiveGraph", "GraphHilbert", "FullSourceDegree", "StableShear", "Tame", "TameShearFactors", "TameShear", "ShearJacobian",
    "FullOutputField", "FullOutputFiber", "FullSourceComponents", "FiberEmbedding", "AlgebraicCoefficientEmbedding", "GeometricGenericDegree", "FullOutputGeometricFiber", "HomogeneousRelations", "ImageRelationNormal", "ImageEquationWitness", "HomogeneousDifferentialDependence", "ConstantPlaneNormal", "PolynomialCoefficientHeight", "ImageRelationHeight", "ImageHypersurface", "ProjectiveImage", "ImageNormalDerivation", "SpanningCoordinates", "NormalSpanDependence", "TwoDirectionNormal", "AffineLineDerivation", "TangentPlaneSpan", "FiberTangentVariation", "PlanarTangentDependence", "PlanarFiberDependence", "GeometricFiberNonlinearity", "ConstantPlaneProjection", "PlaneTranslateDescent", "GeometricPlanarFiber", "FirstOrderTaylor", "HomogeneousEvaluationScaling", "PolynomialDivergence", "RadialTaylorCongruence", "HomogeneousPowerRemoval", "ShearSubstitution", "ShearAutomorphism", "Proposition64", "Main",
]
MODULES.insert(MODULES.index("ShearSubstitution"), "RadialTraceIdentities")
MODULES.insert(MODULES.index("ShearSubstitution"), "RadialTraceObstruction")
MODULES.insert(MODULES.index("ShearSubstitution"), "SaturatedRadialMap")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveCoordinatePoint")
MODULES.insert(MODULES.index("ShearSubstitution"), "GenericOutputPoint")
MODULES.insert(MODULES.index("ShearSubstitution"), "RadialBoundaryEquations")
MODULES.insert(MODULES.index("ShearSubstitution"), "GenericFiberOutput")
MODULES.insert(MODULES.index("ShearSubstitution"), "RadialInfinityExclusion")
MODULES.insert(MODULES.index("ShearSubstitution"), "EulerDerivation")
MODULES.insert(MODULES.index("ShearSubstitution"), "SourceEuler")
MODULES.insert(MODULES.index("ShearSubstitution"), "CoefficientEuler")
MODULES.insert(MODULES.index("ShearSubstitution"), "HomogeneousCoefficientEuler")
MODULES.insert(MODULES.index("ShearSubstitution"), "RadialDerivativeIdentities")
MODULES.insert(MODULES.index("ShearSubstitution"), "WeightedQuadratic")
MODULES.insert(MODULES.index("ShearSubstitution"), "HomogeneousFiberWeights")
MODULES.insert(MODULES.index("ShearSubstitution"), "WeightedFiberInvariants")
MODULES.insert(MODULES.index("ShearSubstitution"), "IsotropicQuadraticCoordinates")
MODULES.insert(MODULES.index("ShearSubstitution"), "IsotropicQuadraticBaseChange")
MODULES.insert(MODULES.index("ShearSubstitution"), "DerivationLineTaylor")
MODULES.insert(MODULES.index("ShearSubstitution"), "RankTwoIsotropicPlane")
MODULES.insert(MODULES.index("ShearSubstitution"), "NormalizedPlaneCoordinates")
MODULES.insert(MODULES.index("ShearSubstitution"), "IsotropicDirectionDifferentiation")
MODULES.insert(MODULES.index("ShearSubstitution"), "CoordinateHessianDirection")
MODULES.insert(MODULES.index("ShearSubstitution"), "HessianDirectionLine")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedCoefficientPartials")
MODULES.insert(MODULES.index("ShearSubstitution"), "CoefficientIsotropicLine")
MODULES.insert(MODULES.index("ShearSubstitution"), "ImageIsotropicLine")
MODULES.insert(MODULES.index("ImageIsotropicLine"), "NormalizedGraphLines")
MODULES.insert(MODULES.index("ShearSubstitution"), "CurvePoleValuation")
MODULES.insert(MODULES.index("ShearSubstitution"), "HomogeneousResidueSpecialization")
MODULES.insert(MODULES.index("ShearSubstitution"), "CubicRadialShift")
MODULES.insert(MODULES.index("ShearSubstitution"), "ValuationResidueCoordinates")
MODULES.insert(MODULES.index("ShearSubstitution"), "CubicRadialBaseChange")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtensionFieldProjectivePoint")
MODULES.insert(MODULES.index("ShearSubstitution"), "BoundaryLeadingEquations")
MODULES.insert(MODULES.index("ShearSubstitution"), "ValuationProjectiveBoundary")
MODULES.insert(MODULES.index("ShearSubstitution"), "BoundaryIsotropicEquations")
MODULES.insert(MODULES.index("ShearSubstitution"), "RadialValuationExclusion")
MODULES.insert(MODULES.index("ShearSubstitution"), "QuadraticPoleOrders")
MODULES.insert(MODULES.index("ShearSubstitution"), "DominantRadialResidue")
MODULES.insert(MODULES.index("ShearSubstitution"), "GenericFiberPoleSeparation")
MODULES.insert(MODULES.index("ShearSubstitution"), "RadialPoleBound")
MODULES.insert(MODULES.index("ShearSubstitution"), "SinglePoleResidueDirection")
MODULES.insert(MODULES.index("ShearSubstitution"), "CubicResidueDescent")
MODULES.insert(MODULES.index("ShearSubstitution"), "SinglePoleCubicIsotropy")
MODULES.insert(MODULES.index("ShearSubstitution"), "GenericFiberSinglePoleBound")
MODULES.insert(MODULES.index("ShearSubstitution"), "GenericFiberCubicIsotropy")
MODULES.insert(MODULES.index("ShearSubstitution"), "QuadraticParameterNonconstancy")
MODULES.insert(MODULES.index("ShearSubstitution"), "GenericFiberTwoCubicDirections")
MODULES.insert(MODULES.index("ShearSubstitution"), "TwoCovectorKernel")
MODULES.insert(MODULES.index("ShearSubstitution"), "ZeroInvariantRadialCovectors")
MODULES.insert(MODULES.index("ShearSubstitution"), "ZeroInvariantFiberLine")
MODULES.insert(MODULES.index("ShearSubstitution"), "ZeroInvariantGeometricFiber")
MODULES.insert(MODULES.index("ShearSubstitution"), "HyperbolaParameterNonconstancy")
MODULES.insert(MODULES.index("ShearSubstitution"), "GenericFiberHyperbolaCubicDirections")
MODULES.insert(MODULES.index("ShearSubstitution"), "RankTwoOrthogonalPair")
MODULES.insert(MODULES.index("ShearSubstitution"), "RankTwoIsotropicBasis")
MODULES.insert(MODULES.index("ShearSubstitution"), "CoefficientIsotropicBasis")
MODULES.insert(MODULES.index("ShearSubstitution"), "GraphIsotropicNormalForm")
MODULES.insert(MODULES.index("ShearSubstitution"), "FiberInvariantTransport")
MODULES.insert(MODULES.index("ShearSubstitution"), "GeometricCoefficientRealization")
MODULES.insert(MODULES.index("ShearSubstitution"), "GeometricCoefficientNormalForm")
MODULES.insert(MODULES.index("ShearSubstitution"), "GeometricFiberIsotropicDirections")
MODULES.insert(MODULES.index("ShearSubstitution"), "RadialDirectionNormalization")
MODULES.insert(MODULES.index("ShearSubstitution"), "NormalizedIsotropicPair")
MODULES.insert(MODULES.index("ShearSubstitution"), "RadialRankTwoBaseChange")
MODULES.insert(MODULES.index("ShearSubstitution"), "GeometricNormalizedDirections")
MODULES.insert(MODULES.index("ShearSubstitution"), "IndependentGraphLines")
MODULES.insert(MODULES.index("ShearSubstitution"), "RealizedCoefficientExtension")
MODULES.insert(MODULES.index("ShearSubstitution"), "GeometricImageTwoLines")
MODULES.insert(MODULES.index("ShearSubstitution"), "RectangularJacobianRank")
MODULES.insert(MODULES.index("ShearSubstitution"), "RationalJacobianCriterion")
MODULES.insert(MODULES.index("ShearSubstitution"), "MatrixRankFieldMap")
MODULES.insert(MODULES.index("ShearSubstitution"), "GaussNormalChart")
MODULES.insert(MODULES.index("ShearSubstitution"), "CoefficientGaussRank")
MODULES.insert(MODULES.index("ShearSubstitution"), "GaussImageDimension")
MODULES.insert(MODULES.index("ShearSubstitution"), "GeometricGaussTwoLines")
MODULES.insert(MODULES.index("ShearSubstitution"), "ThreeSkewLineCoordinates")
MODULES.insert(MODULES.index("ShearSubstitution"), "QuadricTransversals")
MODULES.insert(MODULES.index("ShearSubstitution"), "StandardRulingQuadric")
MODULES.insert(MODULES.index("ShearSubstitution"), "ThreeSkewLineQuadric")
MODULES.insert(MODULES.index("ShearSubstitution"), "ThreeLineQuadricUniqueness")
MODULES.insert(MODULES.index("ShearSubstitution"), "SkewProjectiveLineQuadric")
MODULES.insert(MODULES.index("ShearSubstitution"), "QuadricOppositeRuling")
MODULES.insert(MODULES.index("ShearSubstitution"), "IntersectingLineGeometry")
MODULES.insert(MODULES.index("ShearSubstitution"), "IntersectingLineFamilies")
MODULES.insert(MODULES.index("ShearSubstitution"), "IrreducibleLineFamilies")
MODULES.insert(MODULES.index("ShearSubstitution"), "ConstantGraphDirection")
MODULES.insert(MODULES.index("ShearSubstitution"), "ConstantVertexGaussDimension")
MODULES.insert(MODULES.index("ShearSubstitution"), "GenericVertexLine")
MODULES.insert(MODULES.index("ShearSubstitution"), "GraphLineChart")
MODULES.insert(MODULES.index("ShearSubstitution"), "GraphLineChartTopology")
MODULES.insert(MODULES.index("ShearSubstitution"), "GraphLineEquations")
MODULES.insert(MODULES.index("ShearSubstitution"), "LineChartPivots")
MODULES.insert(MODULES.index("ShearSubstitution"), "LineChartCoverage")
MODULES.insert(MODULES.index("ShearSubstitution"), "HypersurfaceLineAtlas")
MODULES.insert(MODULES.index("ShearSubstitution"), "LineChartNoetherian")
MODULES.insert(MODULES.index("ShearSubstitution"), "HomogeneousProjectiveLine")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveLineAtlasPoints")
MODULES.insert(MODULES.index("ShearSubstitution"), "GeometricLineAtlas")
MODULES.insert(MODULES.index("ShearSubstitution"), "LineChartBaseChange")
MODULES.insert(MODULES.index("ShearSubstitution"), "UniversalLineIncidence")
MODULES.insert(MODULES.index("ShearSubstitution"), "GenericLineCoveringComponent")
MODULES.insert(MODULES.index("ShearSubstitution"), "GenericAtlasLineObstructions")
MODULES.insert(MODULES.index("ShearSubstitution"), "HypersurfaceTangentPlane")
MODULES.insert(MODULES.index("ShearSubstitution"), "PlanarLineCoordinates")
MODULES.insert(MODULES.index("ShearSubstitution"), "PlanarLineFiniteness")
MODULES.insert(MODULES.index("ShearSubstitution"), "LinearPolynomialCoordinates")
MODULES.insert(MODULES.index("ShearSubstitution"), "PointAdaptedCoordinates")
MODULES.insert(MODULES.index("ShearSubstitution"), "PlaneLineFinitenessTransfer")
MODULES.insert(MODULES.index("ShearSubstitution"), "IrreducibleHypersurfaceNoPlane")
MODULES.insert(MODULES.index("ShearSubstitution"), "FiniteLinesAtSmoothPoint")
MODULES.insert(MODULES.index("ShearSubstitution"), "FiniteLineChartFibers")
MODULES.insert(MODULES.index("ShearSubstitution"), "ImageIdealFieldExtension")
MODULES.insert(MODULES.index("ShearSubstitution"), "ScalarExtendedImageEquation")
MODULES.insert(MODULES.index("ShearSubstitution"), "GenericImageLineFiberFiniteness")
MODULES.insert(MODULES.index("ShearSubstitution"), "LineChartEmbedding")
MODULES.insert(MODULES.index("ShearSubstitution"), "UniversalIncidenceFunctionField")
MODULES.insert(MODULES.index("ShearSubstitution"), "CoveringIncidenceAlgebraic")
MODULES.insert(MODULES.index("ShearSubstitution"), "OutputCoordinateFieldEquiv")
MODULES.insert(MODULES.index("ShearSubstitution"), "CoveringLineFamilyDimension")
MODULES.insert(MODULES.index("ShearSubstitution"), "LineComponentPoints")
MODULES.insert(MODULES.index("ShearSubstitution"), "LineComponentSeparation")
MODULES.insert(MODULES.index("ShearSubstitution"), "CoveringLineFamilyObstructions")
MODULES.insert(MODULES.index("ShearSubstitution"), "CoveringLineFamilySkewTriple")
MODULES.insert(MODULES.index("ShearSubstitution"), "CoveringLineFamilyDensity")
MODULES.insert(MODULES.index("ShearSubstitution"), "CoveringTransversalQuadric")
MODULES.insert(MODULES.index("ShearSubstitution"), "TranscendenceDegreeSpecialization")
MODULES.insert(MODULES.index("ShearSubstitution"), "LinePairParameters")
MODULES.insert(MODULES.index("ShearSubstitution"), "LinePairComponentGeometry")
MODULES.insert(MODULES.index("ShearSubstitution"), "GeneratedAlgebraDimension")
MODULES.insert(MODULES.index("ShearSubstitution"), "LinePairComponentDimension")
MODULES.insert(MODULES.index("ShearSubstitution"), "GeneratedFieldDimension")
MODULES.insert(MODULES.index("ShearSubstitution"), "LinePairDimensionDensity")
MODULES.insert(MODULES.index("ShearSubstitution"), "LinePairIncidenceMatrix")
MODULES.insert(MODULES.index("ShearSubstitution"), "TwoDimensionalLinePairQuadric")
MODULES.insert(MODULES.index("ShearSubstitution"), "MatrixKernelDescent")
MODULES.insert(MODULES.index("ShearSubstitution"), "LinePairIntersectionDescent")
MODULES.insert(MODULES.index("ShearSubstitution"), "LinePairGeneratedFieldLowerBound")
MODULES.insert(MODULES.index("ShearSubstitution"), "ActualGenericLinePairQuadric")
MODULES.insert(MODULES.index("ShearSubstitution"), "FiberInvariantDataForWitness")
MODULES.insert(MODULES.index("ShearSubstitution"), "GaussDimensionTwoQuadric")
MODULES.insert(MODULES.index("ShearSubstitution"), "LinearPullbackGradient")
MODULES.insert(MODULES.index("ShearSubstitution"), "NondevelopableImageQuadric")
MODULES.insert(MODULES.index("ShearSubstitution"), "AlgebraicImagePointExtension")
MODULES.insert(MODULES.index("ShearSubstitution"), "RelationGenericCoveringComponent")
MODULES.insert(MODULES.index("ShearSubstitution"), "PolynomialMapScalarExtension")
MODULES.insert(MODULES.index("ShearSubstitution"), "NormalRigidGenericQuadric")
MODULES.insert(MODULES.index("ShearSubstitution"), "ScalarExtendedMapHypotheses")
MODULES.insert(MODULES.index("ShearSubstitution"), "AlgebraicCoefficientQuadric")
MODULES.insert(MODULES.index("ShearSubstitution"), "Proposition31")
MODULES.insert(MODULES.index("Proposition31"), "GradientFieldExtension")
MODULES.insert(MODULES.index("ShearSubstitution"), "GaussImageBound")
MODULES.insert(MODULES.index("ShearSubstitution"), "ZeroDimensionalGaussImage")
MODULES.insert(MODULES.index("ZeroDimensionalGaussImage"), "AlgebraicNormalRatios")
MODULES.insert(MODULES.index("ShearSubstitution"), "GaussImageSurfaceReduction")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveOutputField")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveEulerWeight")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveImageDimension")
MODULES.insert(MODULES.index("ShearSubstitution"), "NormalJacobianGaussDimension")
MODULES.insert(MODULES.index("ShearSubstitution"), "GaussDimensionFieldExtension")
MODULES.insert(MODULES.index("ShearSubstitution"), "PrimitiveLinearIncidence")
MODULES.insert(MODULES.index("ShearSubstitution"), "ParameterizedLinearIncidence")
MODULES.insert(MODULES.index("ShearSubstitution"), "RationalIncidenceSection")
MODULES.insert(MODULES.index("ShearSubstitution"), "ParametrizedNormalRadialExclusion")
MODULES.insert(MODULES.index("ShearSubstitution"), "NonconstantRatioSpecialization")
MODULES.insert(MODULES.index("ShearSubstitution"), "SourceLineRatio")
MODULES.insert(MODULES.index("ShearSubstitution"), "ActualGaussSourceLine")
MODULES.insert(MODULES.index("ShearSubstitution"), "LocalizedRatioRelations")
MODULES.insert(MODULES.index("ShearSubstitution"), "CurveCoordinateSpecialization")
MODULES.insert(MODULES.index("ShearSubstitution"), "GaussCurveLineEmbedding")
MODULES.insert(MODULES.index("ShearSubstitution"), "RationalGaussCurve")
MODULES.insert(MODULES.index("ShearSubstitution"), "PrimitiveRationalVector")
MODULES.insert(MODULES.index("ShearSubstitution"), "GaussCurvePrimitiveParameter")
MODULES.insert(MODULES.index("ShearSubstitution"), "DevelopableRadialExclusion")
MODULES.insert(MODULES.index("ShearSubstitution"), "DevelopableFirstInvariant")
MODULES.insert(MODULES.index("ShearSubstitution"), "RationalParameterDerivation")
MODULES.insert(MODULES.index("ShearSubstitution"), "RationalParameterConstants")
MODULES.insert(MODULES.index("ShearSubstitution"), "DifferentiatedCurveSpan")
MODULES.insert(MODULES.index("ShearSubstitution"), "GaussCurveJetIndependence")
MODULES.insert(MODULES.index("ShearSubstitution"), "GaussCharacteristicSubspaces")
MODULES.insert(MODULES.index("ShearSubstitution"), "GaussRulingIncidence")
MODULES.insert(MODULES.index("ShearSubstitution"), "GaussFiberDimension")
MODULES.insert(MODULES.index("ShearSubstitution"), "MatrixKernelScalarExtension")
MODULES.insert(MODULES.index("ShearSubstitution"), "GraphLineGenericPointDensity")
MODULES.insert(MODULES.index("ShearSubstitution"), "RulingGenericPointDensity")
MODULES.insert(MODULES.index("ShearSubstitution"), "ActualGaussRulingDensity")
MODULES.insert(MODULES.index("ShearSubstitution"), "GaussCharacteristicAlternative")
MODULES.insert(MODULES.index("ShearSubstitution"), "GaussCharacteristicNonplanarity")
MODULES.insert(MODULES.index("ShearSubstitution"), "GaussNormalConstantSpan")
MODULES.insert(MODULES.index("ShearSubstitution"), "CharacteristicPolynomialDegree")
MODULES.insert(MODULES.index("ShearSubstitution"), "ActualGaussNormalSpan")
MODULES.insert(MODULES.index("ShearSubstitution"), "PrimitiveMapDegree")
MODULES.insert(MODULES.index("ShearSubstitution"), "HomogeneousGaussParameter")
MODULES.insert(MODULES.index("ShearSubstitution"), "SourcePencilEquation")
MODULES.insert(MODULES.index("ShearSubstitution"), "GaussPencilDegreeBound")
MODULES.insert(MODULES.index("ShearSubstitution"), "AlgebraicConstantsFinite")
MODULES.insert(MODULES.index("ShearSubstitution"), "FiniteAlgebraicSubextension")
MODULES.insert(MODULES.index("ShearSubstitution"), "ClosedGaussParameterField")
MODULES.insert(MODULES.index("ShearSubstitution"), "RationalSourceCurveField")
MODULES.insert(MODULES.index("ShearSubstitution"), "RationalClosedGaussCover")
MODULES.insert(MODULES.index("ShearSubstitution"), "RelativelyClosedPolynomial")
MODULES.insert(MODULES.index("ShearSubstitution"), "RelativelyClosedFiniteBaseChange")
MODULES.insert(MODULES.index("ShearSubstitution"), "EulerHomogeneousFractions")
MODULES.insert(MODULES.index("ShearSubstitution"), "ClosedGaussHomogeneousParameter")
MODULES.insert(MODULES.index("ShearSubstitution"), "ClosedGaussPencilDegreeBound")
MODULES.insert(MODULES.index("ShearSubstitution"), "RelativelyClosedAlgebraicBaseChange")
MODULES.insert(MODULES.index("ShearSubstitution"), "ClosedGaussCoordinateIntegrality")
MODULES.insert(MODULES.index("ShearSubstitution"), "GenericSourcePencilKernel")
MODULES.insert(MODULES.index("ShearSubstitution"), "ClosedGaussPencilIntegrality")
MODULES.insert(MODULES.index("ShearSubstitution"), "FiniteNormalization")
MODULES.insert(MODULES.index("ShearSubstitution"), "NormalizationRing")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectivePrincipalChart")
MODULES.insert(MODULES.index("ShearSubstitution"), "ClosedGaussPencilCharts")
MODULES.insert(MODULES.index("ShearSubstitution"), "UnramifiedDivisorOrder")
MODULES.insert(MODULES.index("ShearSubstitution"), "SourceDivisorMultiplicity")
MODULES.insert(MODULES.index("ShearSubstitution"), "SourceDivisorLocalization")
MODULES.insert(MODULES.index("ShearSubstitution"), "ClosedGaussExtendedPencilCharts")
MODULES.insert(MODULES.index("ShearSubstitution"), "AdjoinInverseLocalization")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveChartOverlaps")
MODULES.insert(MODULES.index("ShearSubstitution"), "FiniteRelativeNormalization")
MODULES.insert(MODULES.index("ShearSubstitution"), "NormalizationLocalization")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveChartFunctionField")
MODULES.insert(MODULES.index("ShearSubstitution"), "NormalizedCurveEtaleOpen")
MODULES.insert(MODULES.index("ShearSubstitution"), "ActualGaussEtaleCoverModel")
MODULES.insert(MODULES.index("ShearSubstitution"), "ResidueTranscendentalParameter")
MODULES.insert(MODULES.index("ShearSubstitution"), "UnramifiedDvrBaseChange")
MODULES.insert(MODULES.index("ShearSubstitution"), "HorizontalClosedGaussDivisor")
MODULES.insert(MODULES.index("ShearSubstitution"), "IntermediateLocalRing")
MODULES.insert(MODULES.index("ShearSubstitution"), "NormalDvrBaseChange")
MODULES.insert(MODULES.index("ShearSubstitution"), "PencilDivisorParameter")
MODULES.insert(MODULES.index("ShearSubstitution"), "DvrBaseChangeRationalOrder")
MODULES.insert(MODULES.index("ShearSubstitution"), "ActualPencilDivisorLocalModel")
MODULES.insert(MODULES.index("ShearSubstitution"), "SourceLocalNormalization")
MODULES.insert(MODULES.index("ShearSubstitution"), "ClosedGaussCoordinateLocalRing")
MODULES.insert(MODULES.index("ShearSubstitution"), "CoefficientLocalization")
MODULES.insert(MODULES.index("ShearSubstitution"), "CoefficientNormalizedLocalRing")
MODULES.insert(MODULES.index("ShearSubstitution"), "ClosedGaussExtendedLocalRing")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveSourceParameterField")
MODULES.insert(MODULES.index("ShearSubstitution"), "LocalizationFunctionField")
MODULES.insert(MODULES.index("ShearSubstitution"), "CoefficientNormalizationFunctionField")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveSourceCoordinates")
MODULES.insert(MODULES.index("ShearSubstitution"), "PrimeLocalizationFunctionField")
MODULES.insert(MODULES.index("ShearSubstitution"), "RationalCoverHorizontalLocalRing")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveSourceDivisor")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveHorizontalDivisor")
MODULES.insert(MODULES.index("ShearSubstitution"), "AdjoinCoordinateLocalRing")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectivePencilLocalRing")
MODULES.insert(MODULES.index("ShearSubstitution"), "IntermediateFunctionField")
MODULES.insert(MODULES.index("ShearSubstitution"), "ValuationLocalDescent")
MODULES.insert(MODULES.index("ShearSubstitution"), "ValuationCoefficientLocalRing")
MODULES.insert(MODULES.index("ShearSubstitution"), "ValuationLocalOverring")
MODULES.insert(MODULES.index("ShearSubstitution"), "BirationalPrimeLocalRing")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectivePencilFunctionField")
MODULES.insert(MODULES.index("ShearSubstitution"), "BirationalNormalizationLocalRing")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectivePencilContractedPrime")
MODULES.insert(MODULES.index("ShearSubstitution"), "LocalEquivCoefficientField")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectivePencilPrimeParameter")
MODULES.insert(MODULES.index("ShearSubstitution"), "IntermediateDenominatorLocalization")
MODULES.insert(MODULES.index("ShearSubstitution"), "NormalCoordinateLocalization")
MODULES.insert(MODULES.index("ShearSubstitution"), "DenominatorPrimeLocalRing")
MODULES.insert(MODULES.index("ShearSubstitution"), "NormalizedPrimeLocalization")
MODULES.insert(MODULES.index("ShearSubstitution"), "CoefficientSourceCompatibility")
MODULES.insert(MODULES.index("ShearSubstitution"), "SourceDenominatorPrime")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectivePencilPrimeSource")
MODULES.insert(MODULES.index("ShearSubstitution"), "LocalEquivCoordinateLocalization")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveContractedPrimeBaseChange")
MODULES.insert(MODULES.index("ShearSubstitution"), "SourcePrimeLocalExtension")
MODULES.insert(MODULES.index("ShearSubstitution"), "NormalizedPrimeUnramifiedModel")
MODULES.insert(MODULES.index("ShearSubstitution"), "CoordinateLocalizationFunctionField")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectivePencilDenominators")
MODULES.insert(MODULES.index("ShearSubstitution"), "SourceCoefficientExtension")
MODULES.insert(MODULES.index("ShearSubstitution"), "CoefficientCanonicalPrimeModel")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveFinitePrimeModel")
MODULES.insert(MODULES.index("ShearSubstitution"), "CoefficientNormalizationPrimeContraction")
MODULES.insert(MODULES.index("ShearSubstitution"), "PrimeContractionModelTransfer")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveGivenNormalizationPrime")
MODULES.insert(MODULES.index("ShearSubstitution"), "LocalEquivOrderTransport")
MODULES.insert(MODULES.index("ShearSubstitution"), "UnramifiedLocalOrder")
MODULES.insert(MODULES.index("ShearSubstitution"), "LocalEquivSourceMap")
MODULES.insert(MODULES.index("ShearSubstitution"), "LocalEquivUnramifiedSource")
MODULES.insert(MODULES.index("ShearSubstitution"), "LocalEquivRationalOrder")
MODULES.insert(MODULES.index("ShearSubstitution"), "EtaleDivisorLocalProperties")
MODULES.insert(MODULES.index("ShearSubstitution"), "NormalizationLocalSourceOrders")
MODULES.insert(MODULES.index("ShearSubstitution"), "CoefficientCanonicalSourceOrders")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveFiniteSourceOrders")
MODULES.insert(MODULES.index("ShearSubstitution"), "LocalEquivSourceFieldCompatibility")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveGivenSourceOrders")
MODULES.insert(MODULES.index("ShearSubstitution"), "RationalSectionLocalOrder")
MODULES.insert(MODULES.index("ShearSubstitution"), "HomogeneousDehomogenize")
MODULES.insert(MODULES.index("ShearSubstitution"), "HomogenizedDivisorLift")
MODULES.insert(MODULES.index("ShearSubstitution"), "PrimitiveDehomogenization")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveSourceSections")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveChartCommonFactor")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveNormalizationMultiplicity")
MODULES.insert(MODULES.index("ShearSubstitution"), "PrimeLocalOrderConsequences")
MODULES.insert(MODULES.index("ShearSubstitution"), "CoefficientProjectiveMultiplicity")
MODULES.insert(MODULES.index("ShearSubstitution"), "ActualProjectiveNormalizationMultiplicity")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveSourceHeightOne")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveHeightOneMultiplicity")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveSourceImageDivisor")
MODULES.insert(MODULES.index("ShearSubstitution"), "CanonicalSourceLocalMap")
MODULES.insert(MODULES.index("ShearSubstitution"), "CanonicalLocalMapCongruence")
MODULES.insert(MODULES.index("ShearSubstitution"), "ActualProjectiveImageMultiplicity")
MODULES.insert(MODULES.index("ShearSubstitution"), "NormalizationCanonicalOrders")
MODULES.insert(MODULES.index("ShearSubstitution"), "CanonicalRationalOrderComparison")
MODULES.insert(MODULES.index("ShearSubstitution"), "RationalStalkPullbackComparison")
MODULES.insert(MODULES.index("ShearSubstitution"), "FramedRationalStalkComparison")
MODULES.insert(MODULES.index("ShearSubstitution"), "LocalEquivCanonicalRationalOrders")
MODULES.insert(MODULES.index("ShearSubstitution"), "CoefficientCanonicalRegularOrders")
MODULES.insert(MODULES.index("ShearSubstitution"), "CoefficientCanonicalRationalOrders")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveCanonicalRegularOrders")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveCanonicalRationalOrders")
MODULES.insert(MODULES.index("ShearSubstitution"), "ReducedPointClosureScheme")
MODULES.insert(MODULES.index("ShearSubstitution"), "ClosedGaussPencilScheme")
MODULES.insert(MODULES.index("ShearSubstitution"), "IntegralSchemeNormalization")
MODULES.insert(MODULES.index("ShearSubstitution"), "PolynomialProjectiveBase")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveCoefficientMorphism")
MODULES.insert(MODULES.index("ShearSubstitution"), "ClosedGaussPencilNormalizationScheme")
MODULES.insert(MODULES.index("ShearSubstitution"), "GenericPointAffineField")
MODULES.insert(MODULES.index("ShearSubstitution"), "FiniteIntegralSchemeNormalization")
MODULES.insert(MODULES.index("ShearSubstitution"), "IntegralSchemeNormalizationNormal")
MODULES.insert(MODULES.index("ShearSubstitution"), "FiniteClosedGaussPencilScheme")
MODULES.insert(MODULES.index("ShearSubstitution"), "HomogeneousChartEvaluation")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveCoefficientChartMaps")
MODULES.insert(MODULES.index("ShearSubstitution"), "ReducedClosureAffineChart")
MODULES.insert(MODULES.index("ShearSubstitution"), "ReducedClosureChartMorphism")
MODULES.insert(MODULES.index("ShearSubstitution"), "HomogeneousChartPrime")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveSourceSchemeChart")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveSourceChartMorphism")
MODULES.insert(MODULES.index("ShearSubstitution"), "NormalizationCoordinateEquiv")
MODULES.insert(MODULES.index("ShearSubstitution"), "NormalizationAffineCoordinateChart")
MODULES.insert(MODULES.index("ShearSubstitution"), "AffineCoordinateMorphism")
MODULES.insert(MODULES.index("ShearSubstitution"), "NormalizationCoordinateMorphism")
MODULES.insert(MODULES.index("ShearSubstitution"), "AffineChartStalkNaturality")
MODULES.insert(MODULES.index("ShearSubstitution"), "AffineCoordinateStalk")
MODULES.insert(MODULES.index("ShearSubstitution"), "AffineSourcePoint")
MODULES.insert(MODULES.index("ShearSubstitution"), "ClosedGaussPencilSchemeCharts")
MODULES.insert(MODULES.index("ShearSubstitution"), "ClosedGaussNormalizationSchemeCharts")
MODULES.insert(MODULES.index("ShearSubstitution"), "ClosedGaussNormalizationSchemeAtlas")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedGaussPencilPrime")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedGaussPencilScheme")
MODULES.insert(MODULES.index("ShearSubstitution"), "DehomogenizedBaseChange")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveCoefficientChartEquiv")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedGaussRatioCoordinates")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedGaussSourceCoordinates")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedGaussSourceNormalization")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedGaussSchemeTensorCharts")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedGaussSchemeTensorAtlas")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedGaussNormalizationMorphism")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedGaussSourceMorphism")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedGaussSourceFractions")
MODULES.insert(MODULES.index("ShearSubstitution"), "OriginalProjectiveChartRing")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedGaussProjectiveSections")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedGaussPencilSourceDiagram")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedGaussNormalizationSourceDiagram")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedGaussSourcePoint")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedGaussNormalizationStalkMaps")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedGaussProjectiveStalkMaps")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedGaussStalkOrders")
MODULES.insert(MODULES.index("ShearSubstitution"), "GlobalNormalizationMultiplicity")
MODULES.insert(MODULES.index("ShearSubstitution"), "OriginalSourcePrimeRegularOrders")
MODULES.insert(MODULES.index("ShearSubstitution"), "OriginalSourceCanonicalOrders")
MODULES.insert(MODULES.index("ShearSubstitution"), "OriginalSourceCanonicalRationalOrders")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedGaussSourceStalk")
MODULES.insert(MODULES.index("ShearSubstitution"), "GeometricSourceStalkOrders")
MODULES.insert(MODULES.index("ShearSubstitution"), "GlobalCanonicalRationalOrders")
MODULES.insert(MODULES.index("ShearSubstitution"), "GeometricRationalSourceOrders")
MODULES.insert(MODULES.index("ShearSubstitution"), "GeometricRationalSectionOrders")
MODULES.insert(MODULES.index("ShearSubstitution"), "GeometricSourceMultiplicity")
MODULES.insert(MODULES.index("ShearSubstitution"), "GlobalNormalizationRegularOrders")
MODULES.insert(MODULES.index("ShearSubstitution"), "AffineStalkDimension")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedGaussPointAtlas")
MODULES.insert(MODULES.index("ShearSubstitution"), "GlobalSourceCodimension")
MODULES.insert(MODULES.index("ShearSubstitution"), "GlobalPointRegularOrders")
MODULES.insert(MODULES.index("ShearSubstitution"), "RationalComparisonFractionField")
MODULES.insert(MODULES.index("ShearSubstitution"), "IntrinsicDivisorPullback")
MODULES.insert(MODULES.index("ShearSubstitution"), "SchemeDivisorPullback")
MODULES.insert(MODULES.index("ShearSubstitution"), "PolynomialProjectiveProperties")
MODULES.insert(MODULES.index("ShearSubstitution"), "GlobalPointDivisorOrders")
MODULES.insert(MODULES.index("ShearSubstitution"), "GlobalDivisorImagePrime")
MODULES.insert(MODULES.index("ShearSubstitution"), "GlobalCurveDivisorOrders")
MODULES.insert(MODULES.index("ShearSubstitution"), "GlobalSchemeDivisorOrders")
MODULES.insert(MODULES.index("ShearSubstitution"), "ReducedClosureLift")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedGaussPencilOriginalMap")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveCoefficientEvaluation")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedGaussPencilCoefficientSections")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedGaussPencilOriginalChartMap")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveCoefficientBaseMap")
MODULES.insert(MODULES.index("ShearSubstitution"), "ClosedGaussPencilOriginalAtlas")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveChartBaseMap")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedGaussPencilBaseChangeComparison")
MODULES.insert(MODULES.index("ShearSubstitution"), "SchemeBaseChangeCharts")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedGaussPencilChartBaseMaps")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedGaussPencilCartesianCharts")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedGaussPencilBaseChange")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveCoefficientComposition")
MODULES.insert(MODULES.index("ShearSubstitution"), "ClosedGaussPencilBaseChangeSource")
MODULES.insert(MODULES.index("ShearSubstitution"), "RelativeNormalizationIso")
MODULES.insert(MODULES.index("ShearSubstitution"), "IntegralSchemeFunctionFieldIso")
MODULES.insert(MODULES.index("ShearSubstitution"), "IntegralSchemeNormalizationIso")
MODULES.insert(MODULES.index("ShearSubstitution"), "ClosedGaussPencilBaseChangeNormalization")
MODULES.insert(MODULES.index("ShearSubstitution"), "IntrinsicDivisorPullbackEquiv")
MODULES.insert(MODULES.index("ShearSubstitution"), "SchemeDivisorPullbackIso")
MODULES.insert(MODULES.index("ShearSubstitution"), "ClosedGaussPencilBaseChangeNormalizationProperties")
MODULES.insert(MODULES.index("ShearSubstitution"), "CategoricalPencilDivisorOrders")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectivePointCommonFactor")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveSectionOrderMultiplicity")
MODULES.insert(MODULES.index("ShearSubstitution"), "CategoricalPencilCommonFactor")
MODULES.insert(MODULES.index("ShearSubstitution"), "SchemeRegularOrderBounds")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveSectionIntegerOrders")
MODULES.insert(MODULES.index("ShearSubstitution"), "CategoricalPencilIntegerMultiplicity")
MODULES.insert(MODULES.index("ShearSubstitution"), "CategoricalPencilBaseField")
MODULES.insert(MODULES.index("ShearSubstitution"), "SchemeSpreadOutImage")
MODULES.insert(MODULES.index("ShearSubstitution"), "RationalCoverParameterScheme")
MODULES.insert(MODULES.index("ShearSubstitution"), "SchemeParameterSpread")
MODULES.insert(MODULES.index("ShearSubstitution"), "ClosedGaussParameterCurveScheme")
MODULES.insert(MODULES.index("ShearSubstitution"), "ClosedGaussPencilSpreadScheme")
MODULES.insert(MODULES.index("ShearSubstitution"), "SpreadOutPencilDivisorOrders")
MODULES.insert(MODULES.index("ShearSubstitution"), "SchemeFramedDivisorPullback")
MODULES.insert(MODULES.index("ShearSubstitution"), "Lemma42")
MODULES.insert(MODULES.index("ShearSubstitution"), "FiniteFlatRamificationBound")
MODULES.insert(MODULES.index("ShearSubstitution"), "DvrOrderQuotientLength")
MODULES.insert(MODULES.index("ShearSubstitution"), "FiniteFlatDvrMultiplicity")
MODULES.insert(MODULES.index("ShearSubstitution"), "DvrNormalizationMultiplicity")
MODULES.insert(MODULES.index("ShearSubstitution"), "DedekindLocalOverring")
MODULES.insert(MODULES.index("ShearSubstitution"), "DominatingDvrMultiplicity")
MODULES.insert(MODULES.index("ShearSubstitution"), "SimpleFieldDegreeBound")
MODULES.insert(MODULES.index("ShearSubstitution"), "DvrPolynomialMultiplicity")
MODULES.insert(MODULES.index("ShearSubstitution"), "ResidueParameterField")
MODULES.insert(MODULES.index("ShearSubstitution"), "LocalParameterDvr")
MODULES.insert(MODULES.index("ShearSubstitution"), "LocalParameterFractionField")
MODULES.insert(MODULES.index("ShearSubstitution"), "LocalParameterProjectionField")
MODULES.insert(MODULES.index("ShearSubstitution"), "LocalCoordinateMultiplicity")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectionDefiningPolynomial")
MODULES.insert(MODULES.index("ShearSubstitution"), "HypersurfaceLocalMultiplicity")
MODULES.insert(MODULES.index("ShearSubstitution"), "TwoParameterProjection")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectionFieldGenerator")
MODULES.insert(MODULES.index("ShearSubstitution"), "ResidueParameterAlgebra")
MODULES.insert(MODULES.index("ShearSubstitution"), "ResidueCoordinateProjection")
MODULES.insert(MODULES.index("ShearSubstitution"), "ThreeCoordinateMultiplicity")
MODULES.insert(MODULES.index("ShearSubstitution"), "TranscendentalResidueCoordinate")
MODULES.insert(MODULES.index("ShearSubstitution"), "AffineMaximalHeight")
MODULES.insert(MODULES.index("ShearSubstitution"), "GeneratedCoordinateFractionField")
MODULES.insert(MODULES.index("ShearSubstitution"), "HeightOneResidueCoordinate")
MODULES.insert(MODULES.index("ShearSubstitution"), "ThreeCoordinateResidueChoice")
MODULES.insert(MODULES.index("ShearSubstitution"), "AffineCoordinateMultiplicity")
MODULES.insert(MODULES.index("ShearSubstitution"), "NormalizedAffineCoordinateMultiplicity")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectivePencilDimension")
MODULES.insert(MODULES.index("ShearSubstitution"), "PencilChartCoordinateMultiplicity")
MODULES.insert(MODULES.index("ShearSubstitution"), "AlgebraicCoordinateBaseChange")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedPencilCoordinateMultiplicity")
MODULES.insert(MODULES.index("ShearSubstitution"), "AffineSubstitutionDegree")
MODULES.insert(MODULES.index("ShearSubstitution"), "AffinePivotCoordinates")
MODULES.insert(MODULES.index("ShearSubstitution"), "AffineCoordinateGeneration")
MODULES.insert(MODULES.index("ShearSubstitution"), "NormalizedAffineLinearMultiplicity")
MODULES.insert(MODULES.index("ShearSubstitution"), "ThreeAffineHyperplaneMultiplicity")
MODULES.insert(MODULES.index("ShearSubstitution"), "TensorPencilHyperplaneMultiplicity")
MODULES.insert(MODULES.index("ShearSubstitution"), "GlobalPencilHyperplaneMultiplicity")
MODULES.insert(MODULES.index("ShearSubstitution"), "GlobalPencilHyperplaneAtlas")
MODULES.insert(MODULES.index("ShearSubstitution"), "DvrNormOrderBound")
MODULES.insert(MODULES.index("ShearSubstitution"), "PolynomialNormOrderBound")
MODULES.insert(MODULES.index("ShearSubstitution"), "RationalInfinityDegree")
MODULES.insert(MODULES.index("ShearSubstitution"), "RationalNormDegree")
MODULES.insert(MODULES.index("ShearSubstitution"), "PolynomialNormalizationSectionBound")
MODULES.insert(MODULES.index("ShearSubstitution"), "NormalLocalSectionBound")
MODULES.insert(MODULES.index("ShearSubstitution"), "NormalLocalHypersurfaceSectionBound")
MODULES.insert(MODULES.index("ShearSubstitution"), "InfinityScaledMonicRoot")
MODULES.insert(MODULES.index("ShearSubstitution"), "MonicProjectionSection")
MODULES.insert(MODULES.index("ShearSubstitution"), "MonicProjectionSectionBound")
MODULES.insert(MODULES.index("ShearSubstitution"), "MonicHypersurfaceProjection")
MODULES.insert(MODULES.index("ShearSubstitution"), "HypersurfaceProjectionSectionBound")
MODULES.insert(MODULES.index("ShearSubstitution"), "LinearMonicProjectionChoice")
MODULES.insert(MODULES.index("ShearSubstitution"), "LinearProjectionCoordinateChange")
MODULES.insert(MODULES.index("ShearSubstitution"), "ConstructedMonicProjectionCoordinates")
MODULES.insert(MODULES.index("ShearSubstitution"), "MonicAffineFiniteProjection")
MODULES.insert(MODULES.index("ShearSubstitution"), "ConstructedAffineFiniteProjection")
MODULES.insert(MODULES.index("ShearSubstitution"), "TensorPencilFiniteProjection")
MODULES.insert(MODULES.index("ShearSubstitution"), "ValuativeIntegralCriterion")
MODULES.insert(MODULES.index("ShearSubstitution"), "ValuationProjectiveLinearFrame")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveNormalizedSection")
MODULES.insert(MODULES.index("ShearSubstitution"), "ScaledProjectionCoordinateIntegrality")
MODULES.insert(MODULES.index("ShearSubstitution"), "RationalProjectionCoordinateIntegrality")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveSectionProjectionRegularity")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectionGeneratorOriginalField")
MODULES.insert(MODULES.index("ShearSubstitution"), "OriginalChartProjectiveSectionBound")
MODULES.insert(MODULES.index("ShearSubstitution"), "FiniteProjectionIndependence")
MODULES.insert(MODULES.index("ShearSubstitution"), "FiniteProjectionResidueParameter")
MODULES.insert(MODULES.index("ShearSubstitution"), "CanonicalProjectionResidueParameter")
MODULES.insert(MODULES.index("ShearSubstitution"), "TensorPencilProjectionResidue")
MODULES.insert(MODULES.index("ShearSubstitution"), "IndependentRationalProjection")
MODULES.insert(MODULES.index("ShearSubstitution"), "IndependentProjectionField")
MODULES.insert(MODULES.index("ShearSubstitution"), "ResidueIndependentProjectionField")
MODULES.insert(MODULES.index("ShearSubstitution"), "ResidueProjectionPolynomialActions")
MODULES.insert(MODULES.index("ShearSubstitution"), "RationalInfinityTargetAction")
MODULES.insert(MODULES.index("ShearSubstitution"), "FiniteProjectionLocalCenter")
MODULES.insert(MODULES.index("ShearSubstitution"), "OriginalChartNonfieldSectionBound")
MODULES.insert(MODULES.index("ShearSubstitution"), "ResidueProjectionActionCompatibility")
MODULES.insert(MODULES.index("ShearSubstitution"), "NormalizationPrimeFunctionField")
MODULES.insert(MODULES.index("ShearSubstitution"), "CanonicalProjectionFieldActions")
MODULES.insert(MODULES.index("ShearSubstitution"), "TensorPencilProjectionFieldActions")
MODULES.insert(MODULES.index("ShearSubstitution"), "OriginalChartResidueProjectionBound")
MODULES.insert(MODULES.index("ShearSubstitution"), "CanonicalOriginalChartSectionBound")
MODULES.insert(MODULES.index("ShearSubstitution"), "ReindexedProjectiveSectionRegularity")
MODULES.insert(MODULES.index("ShearSubstitution"), "ReindexedProjectionFieldGenerator")
MODULES.insert(MODULES.index("ShearSubstitution"), "ReindexedOriginalChartSectionBound")
MODULES.insert(MODULES.index("ShearSubstitution"), "ReindexedResidueProjectionBound")
MODULES.insert(MODULES.index("ShearSubstitution"), "SelectedProjectionCoordinates")
MODULES.insert(MODULES.index("ShearSubstitution"), "CanonicalFiniteProjectionSectionBound")
MODULES.insert(MODULES.index("ShearSubstitution"), "ConstructedOriginalSectionBound")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveAffineRatioCoordinates")
MODULES.insert(MODULES.index("ShearSubstitution"), "TensorPencilOriginalSectionMultiplicity")
MODULES.insert(MODULES.index("ShearSubstitution"), "OriginalChartSectionCoefficient")
MODULES.insert(MODULES.index("ShearSubstitution"), "OriginalChartCanonicalSectionOrder")
MODULES.insert(MODULES.index("ShearSubstitution"), "TensorPencilCanonicalSectionMultiplicity")
MODULES.insert(MODULES.index("ShearSubstitution"), "OriginalChartSectionStalkTransport")
MODULES.insert(MODULES.index("ShearSubstitution"), "GlobalOriginalSectionMultiplicity")
MODULES.insert(MODULES.index("ShearSubstitution"), "NormalDivisorStalkDvr")
MODULES.insert(MODULES.index("ShearSubstitution"), "NormalizedHyperplaneTransitions")
MODULES.insert(MODULES.index("ShearSubstitution"), "RegularSectionIntegerMultiplicity")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedNormalizationDivisorDvr")
MODULES.insert(MODULES.index("ShearSubstitution"), "NormalizedHyperplaneGluing")
MODULES.insert(MODULES.index("ShearSubstitution"), "NormalizedHyperplaneCocycle")
MODULES.insert(MODULES.index("ShearSubstitution"), "OriginalSectionGermNonzero")
MODULES.insert(MODULES.index("ShearSubstitution"), "RegularFrameIntegerOrder")
MODULES.insert(MODULES.index("ShearSubstitution"), "GlobalHyperplaneIntegerMultiplicity")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedNormalizedChartSections")
MODULES.insert(MODULES.index("ShearSubstitution"), "SchemeRationalSectionFunctions")
MODULES.insert(MODULES.index("ShearSubstitution"), "RationalFrameLocalPredicate")
MODULES.insert(MODULES.index("ShearSubstitution"), "RationalFrameSectionSubmodule")
MODULES.insert(MODULES.index("ShearSubstitution"), "RationalFrameModuleSheaf")
MODULES.insert(MODULES.index("ShearSubstitution"), "SchemeLocallyRegularRationalFunctions")
MODULES.insert(MODULES.index("ShearSubstitution"), "RationalFrameLocalCoefficient")
MODULES.insert(MODULES.index("ShearSubstitution"), "RationalFrameRegularCoefficient")
MODULES.insert(MODULES.index("ShearSubstitution"), "RationalFrameLocalTrivialization")
MODULES.insert(MODULES.index("ShearSubstitution"), "RationalFrameLineBundle")
MODULES.insert(MODULES.index("ShearSubstitution"), "RationalFrameGlobalSections")
MODULES.insert(MODULES.index("ShearSubstitution"), "RationalFrameGlobalGluing")
MODULES.insert(MODULES.index("ShearSubstitution"), "AffineChartFunctionFieldEquiv")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedNormalizationFunctionField")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveCoordinateRatioSections")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectivePullbackRationalCoordinates")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectivePullbackHyperplaneSheaf")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedNormalizationHyperplaneSheaf")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedNormalizationHyperplaneSections")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedNormalizationHyperplaneGluing")
MODULES.insert(MODULES.index("ShearSubstitution"), "AffineChartSectionNaturality")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedNormalizedChartPullbacks")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveCoordinateRatioEvaluation")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedPencilAmbientPullbacks")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedNormalizedAmbientValues")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveConstantSections")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedNormalizedCoefficientValues")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveChartThreeGenerators")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedOwnCoordinateCharts")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedNativeNormalizedSections")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveNormalizedSectionFieldMap")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedOwnFunctionFieldEquiv")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedOriginalSectionRepresentation")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedNormalizedChartGerms")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedNativeSectionGerms")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedNativeSectionMultiplicity")
MODULES.insert(MODULES.index("ShearSubstitution"), "NormalSchemeRationalRoots")
MODULES.insert(MODULES.index("ShearSubstitution"), "RationalFramePowers")
MODULES.insert(MODULES.index("ShearSubstitution"), "RationalFrameRootExtension")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveHomogeneousPullbackCoefficients")
MODULES.insert(MODULES.index("ShearSubstitution"), "RationalFramePowerFrames")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveHomogeneousPullbackSections")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedHomogeneousPowerSections")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedRationalRootSections")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedHomogeneousSectionCoefficients")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedRationalRootMultiplicity")
MODULES.insert(MODULES.index("ShearSubstitution"), "SchemeIntegerOrderArithmetic")
MODULES.insert(MODULES.index("ShearSubstitution"), "RationalFrameGlobalValueArithmetic")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedFrameIntegerOrders")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedNativeLinearCombinations")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedProductPowerMultiplicity")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedSourceFormLocalIdeals")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedOutputSpanMultiplicity")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveChartPolynomialSections")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveChartPolynomialCoefficientChange")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedNativeSourceFormPullbacks")
MODULES.insert(MODULES.index("ShearSubstitution"), "NativePencilCommonFactorContradiction")
MODULES.insert(MODULES.index("ShearSubstitution"), "ReducedHomogeneousPencilDegree")
MODULES.insert(MODULES.index("ShearSubstitution"), "NativePencilSpreadFamily")
MODULES.insert(MODULES.index("ShearSubstitution"), "RulingRootProductIdentity")
MODULES.insert(MODULES.index("ShearSubstitution"), "NativePencilSourceDivisorExclusion")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedOriginalHomogeneousRelations")
MODULES.insert(MODULES.index("ShearSubstitution"), "RulingFormCoordinateSpan")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedParameterOutputRelations")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedActualGaussRuling")
MODULES.insert(MODULES.index("ShearSubstitution"), "RulingFormRelations")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedChosenGaussRuling")
MODULES.insert(MODULES.index("ShearSubstitution"), "NativeIndependentRulingExclusion")
MODULES.insert(MODULES.index("ShearSubstitution"), "PolynomialCovectorCoefficientKernel")
MODULES.insert(MODULES.index("ShearSubstitution"), "SmallKernelScalarExtension")
MODULES.insert(MODULES.index("ShearSubstitution"), "NormalPlaneConstantIntersection")
MODULES.insert(MODULES.index("ShearSubstitution"), "PolynomialPlaneParameterRigidity")
MODULES.insert(MODULES.index("ShearSubstitution"), "MovingPlanePointFieldDimension")
MODULES.insert(MODULES.index("ShearSubstitution"), "ActualGaussPlaneFixedCurve")
MODULES.insert(MODULES.index("ShearSubstitution"), "IntegralCoordinateFieldGeneration")
MODULES.insert(MODULES.index("ShearSubstitution"), "NormalizationResidueCoordinateField")
MODULES.insert(MODULES.index("ShearSubstitution"), "RationalParameterCoefficientAlgebraicity")
MODULES.insert(MODULES.index("ShearSubstitution"), "ClosedGaussCoefficientImages")
MODULES.insert(MODULES.index("ShearSubstitution"), "TensorPencilResidueFieldGeneration")
MODULES.insert(MODULES.index("ShearSubstitution"), "NormalizationResidueDimension")
MODULES.insert(MODULES.index("ShearSubstitution"), "AffineGeneratedPointCoordinates")
MODULES.insert(MODULES.index("ShearSubstitution"), "AffinePointFieldDimension")
MODULES.insert(MODULES.index("ShearSubstitution"), "TensorPencilResidueDimension")
MODULES.insert(MODULES.index("ShearSubstitution"), "TensorPencilResiduePointDimension")
MODULES.insert(MODULES.index("ShearSubstitution"), "NormalizationResidueDimensionExact")
MODULES.insert(MODULES.index("ShearSubstitution"), "TensorPencilResidueDimensionExact")
MODULES.insert(MODULES.index("ShearSubstitution"), "PrimeQuotientCodimensionOne")
MODULES.insert(MODULES.index("ShearSubstitution"), "GeneratedPointPrimeDimension")
MODULES.insert(MODULES.index("ShearSubstitution"), "TensorPencilResidueSourcePrime")
MODULES.insert(MODULES.index("ShearSubstitution"), "TensorPencilMovingPlaneSourceDivisor")
MODULES.insert(MODULES.index("ShearSubstitution"), "RationalPlanePolynomialSpecialization")
MODULES.insert(MODULES.index("ShearSubstitution"), "ActualGaussPlaneSpecialization")
MODULES.insert(MODULES.index("ShearSubstitution"), "TensorPencilActualGaussPlane")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedRootCombinationVanishing")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedInputLinearCoefficient")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedInputLinearResidue")
MODULES.insert(MODULES.index("ShearSubstitution"), "ActualRootVanishingSourceDivisor")
MODULES.insert(MODULES.index("ShearSubstitution"), "ActualGaussIndependentRootExclusion")
MODULES.insert(MODULES.index("ShearSubstitution"), "PrincipalVanishingDivisor")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedNonunitSectionDivisor")
MODULES.insert(MODULES.index("ShearSubstitution"), "ActualGaussRootUnitCoefficients")
MODULES.insert(MODULES.index("ShearSubstitution"), "RadialIntegralUnitObstruction")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveConeCoordinateAlgebra")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedOwnCoordinateFieldGeneration")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveConeFractionConstants")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedNativeCone")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveConeRootLift")
MODULES.insert(MODULES.index("ShearSubstitution"), "NormalizationDivisorNonvertex")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedNativeConeNormalization")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedNativeConeRoots")
MODULES.insert(MODULES.index("ShearSubstitution"), "UnitSectionCoefficientInverseIntegral")
MODULES.insert(MODULES.index("ShearSubstitution"), "NormalizationConeChartObstruction")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedNativeConeZeroTransfer")
MODULES.insert(MODULES.index("ShearSubstitution"), "IndependentGaussRootConfigurationExclusion")
MODULES.insert(MODULES.index("ShearSubstitution"), "ActualRootDivisorSpreadConstruction")
MODULES.insert(MODULES.index("ShearSubstitution"), "DerivationSurfaceConstants")
MODULES.insert(MODULES.index("ShearSubstitution"), "WeightedAffineRootFactorization")
MODULES.insert(MODULES.index("ShearSubstitution"), "AlgebraicBinaryRootFactorization")
MODULES.insert(MODULES.index("ShearSubstitution"), "ModifiedCubicFiberBoundary")
MODULES.insert(MODULES.index("ShearSubstitution"), "ParametricGraphHessian")
MODULES.insert(MODULES.index("ShearSubstitution"), "SymmetrizedCubicFactor")
MODULES.insert(MODULES.index("ShearSubstitution"), "ParametricGraphCubic")
MODULES.insert(MODULES.index("ShearSubstitution"), "ClosedGaussCoefficientRealization")
MODULES.insert(MODULES.index("ShearSubstitution"), "RulingDirectionAcceleration")
MODULES.insert(MODULES.index("ShearSubstitution"), "ActualDevelopableGraphEquations")
MODULES.insert(MODULES.index("ShearSubstitution"), "ParametricGraphBaseChange")
MODULES.insert(MODULES.index("ShearSubstitution"), "ActualDevelopableBoundaryEquation")
MODULES.insert(MODULES.index("ShearSubstitution"), "ActualFiberBoundaryExistence")
MODULES.insert(MODULES.index("ShearSubstitution"), "ActualDevelopableBoundaryWitness")
MODULES.insert(MODULES.index("ShearSubstitution"), "ActualDevelopableBoundaryConstruction")
MODULES.insert(MODULES.index("ActualDevelopableBoundaryWitness"), "CurveValuationResidueAlgebraic")
MODULES.insert(MODULES.index("ActualDevelopableBoundaryWitness"), "ActualFiberBoundaryResidue")
MODULES.insert(MODULES.index("ShearSubstitution"), "NilpotentFunctionalTransport")
MODULES.insert(MODULES.index("ShearSubstitution"), "ResidueTangentLattice")
MODULES.insert(MODULES.index("ShearSubstitution"), "SimplePoleTangentAction")
MODULES.insert(MODULES.index("ShearSubstitution"), "SimplePoleNilpotentObstruction")
MODULES.insert(MODULES.index("ShearSubstitution"), "NormalizedJacobianSimplePole")
MODULES.insert(MODULES.index("ShearSubstitution"), "RationalParameterTangentTransport")
MODULES.insert(MODULES.index("ShearSubstitution"), "SourceConeParameterObstruction")
MODULES.insert(MODULES.index("ShearSubstitution"), "ConeTangentParameterObstruction")
MODULES.insert(MODULES.index("ShearSubstitution"), "TranscendentalSeparatingDerivation")
MODULES.insert(MODULES.index("ShearSubstitution"), "ConeParameterDifferential")
MODULES.insert(MODULES.index("ShearSubstitution"), "ImageConeGaussRealization")
MODULES.insert(MODULES.index("ShearSubstitution"), "DominantConeGaussRestriction")
MODULES.insert(MODULES.index("ShearSubstitution"), "ConeTangentDerivation")
MODULES.insert(MODULES.index("ShearSubstitution"), "ConeGaussTangentDifferential")
MODULES.insert(MODULES.index("ShearSubstitution"), "OriginalConeRulingKernel")
MODULES.insert(MODULES.index("ShearSubstitution"), "FixedNormalKernelTransport")
MODULES.insert(MODULES.index("ShearSubstitution"), "ConeGaussHomogeneousFraction")
MODULES.insert(MODULES.index("ShearSubstitution"), "Lemma43ConeRestriction")
MODULES.insert(MODULES.index("ShearSubstitution"), "Lemma43ProjectiveRestriction")
MODULES.insert(MODULES.index("ShearSubstitution"), "PrimitiveBoundaryImage")
MODULES.insert(MODULES.index("ShearSubstitution"), "HomogeneousProjectiveSubstitution")
MODULES.insert(MODULES.index("ShearSubstitution"), "ActualFullFiberBoundary")
MODULES.insert(MODULES.index("ShearSubstitution"), "PrimitiveBoundaryParameter")
MODULES.insert(MODULES.index("ShearSubstitution"), "ActualBoundaryTargetGeneric")
MODULES.insert(MODULES.index("ShearSubstitution"), "ActualBoundaryDirectionDominance")
MODULES.insert(MODULES.index("ShearSubstitution"), "RulingScalarExtensionDensity")
MODULES.insert(MODULES.index("ShearSubstitution"), "ActualRulingGaussParameter")
MODULES.insert(MODULES.index("ShearSubstitution"), "ActualBoundaryRulingParameter")
MODULES.insert(MODULES.index("ShearSubstitution"), "ActualBoundaryRulingExclusion")
MODULES.insert(MODULES.index("ShearSubstitution"), "OriginalGaussGraphCoordinates")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveClosureLeadingEquations")
MODULES.insert(MODULES.index("ShearSubstitution"), "GraphNormalParameterRuling")
MODULES.insert(MODULES.index("ShearSubstitution"), "ActualFullBoundaryOriginalRuling")
MODULES.insert(MODULES.index("ShearSubstitution"), "ActualBoundaryNonGeneric")
MODULES.insert(MODULES.index("ShearSubstitution"), "AlgebraicProjectiveLineRoots")
MODULES.insert(MODULES.index("ShearSubstitution"), "NormalizedRulingAlgebraicity")
MODULES.insert(MODULES.index("ShearSubstitution"), "ActualBoundaryGaussAlgebraicity")
MODULES.insert(MODULES.index("ShearSubstitution"), "FiniteGaussBoundaryBranch")
MODULES.insert(MODULES.index("ShearSubstitution"), "BoundaryGaussFieldComparison")
MODULES.insert(MODULES.index("ShearSubstitution"), "ActualGaussBoundaryAcceleration")
MODULES.insert(MODULES.index("ShearSubstitution"), "ActualFiniteGaussBoundaryConstruction")
MODULES.insert(MODULES.index("ShearSubstitution"), "OriginalMapFiniteGaussBoundary")
MODULES.insert(MODULES.index("ShearSubstitution"), "GaussParameterSurfaceDimension")
MODULES.insert(MODULES.index("ShearSubstitution"), "WeightedRulingCoordinates")
MODULES.insert(MODULES.index("ShearSubstitution"), "ParametricWeightedRulingFactorization")
MODULES.insert(MODULES.index("ShearSubstitution"), "ParametricLinearRootForms")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedCoefficientEuler")
MODULES.insert(MODULES.index("ShearSubstitution"), "ActualWeightedGaussRootForms")
MODULES.insert(MODULES.index("ShearSubstitution"), "ActualBoundaryGraphDirection")
MODULES.insert(MODULES.index("ShearSubstitution"), "ActualGaussBoundaryRootConstruction")
MODULES.insert(MODULES.index("ShearSubstitution"), "OriginalMapGaussRootForms")
MODULES.insert(MODULES.index("ShearSubstitution"), "ClosedGaussCoefficientTensor")
MODULES.insert(MODULES.index("ShearSubstitution"), "FaithfulCoefficientTensor")
MODULES.insert(MODULES.index("ShearSubstitution"), "ScalarExtendedSourceRelations")
MODULES.insert(MODULES.index("ShearSubstitution"), "NativeHomogeneousSourceRelations")
MODULES.insert(MODULES.index("ShearSubstitution"), "FiniteCoefficientScalarEquiv")
MODULES.insert(MODULES.index("ShearSubstitution"), "ParameterImageFiniteExtension")
MODULES.insert(MODULES.index("ShearSubstitution"), "CoefficientSourceTensor")
MODULES.insert(MODULES.index("ShearSubstitution"), "ClosedGaussInvariantLinearForm")
MODULES.insert(MODULES.index("ShearSubstitution"), "NativeRationalRootTransfer")
MODULES.insert(MODULES.index("ShearSubstitution"), "BoundaryRationalRootTensor")
MODULES.insert(MODULES.index("ShearSubstitution"), "SourceTensorPolynomialValues")
MODULES.insert(MODULES.index("ShearSubstitution"), "ActualBoundaryNativeRoot")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedHomogeneousRootExistence")
MODULES.insert(MODULES.index("ShearSubstitution"), "NativeRootNonvanishingTransfer")
MODULES.insert(MODULES.index("ShearSubstitution"), "ActualNativeRootNonzero")
MODULES.insert(MODULES.index("ShearSubstitution"), "ActualFiniteNativeRootConstruction")
MODULES.insert(MODULES.index("ShearSubstitution"), "OriginalMapNativeRootForms")
MODULES.insert(MODULES.index("ShearSubstitution"), "ClosedGaussNormalComparison")
MODULES.insert(MODULES.index("ShearSubstitution"), "SelectedOutputCovectors")
MODULES.insert(MODULES.index("ShearSubstitution"), "NativeGraphNormalComparison")
MODULES.insert(MODULES.index("ShearSubstitution"), "NativeChosenRootForms")
MODULES.insert(MODULES.index("ShearSubstitution"), "TwoDimensionalFormAlternatives")
MODULES.insert(MODULES.index("ShearSubstitution"), "RulingFormNonvanishing")
MODULES.insert(MODULES.index("ShearSubstitution"), "ActualChosenRootAlternatives")
MODULES.insert(MODULES.index("ShearSubstitution"), "ConstructedRulingProductPower")
MODULES.insert(MODULES.index("ShearSubstitution"), "RulingCoordinateBasis")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProportionalRootFieldIdentities")
MODULES.insert(MODULES.index("ShearSubstitution"), "NativeProportionalRootIdentities")
MODULES.insert(MODULES.index("ShearSubstitution"), "NativeProportionalPowerFactorization")
MODULES.insert(MODULES.index("ShearSubstitution"), "FiniteChosenRootConstruction")
MODULES.insert(MODULES.index("ShearSubstitution"), "OriginalMapRootAlternatives")
MODULES.insert(MODULES.index("ShearSubstitution"), "RationalCoverJetComparison")
MODULES.insert(MODULES.index("ShearSubstitution"), "GaussRootNumeratorCoefficients")
MODULES.insert(MODULES.index("ShearSubstitution"), "GraphNormalSecondJet")
MODULES.insert(MODULES.index("ShearSubstitution"), "GraphDenominatorCharacteristic")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedChosenGaussCharacteristic")
MODULES.insert(MODULES.index("ShearSubstitution"), "ActualRootCharacteristicComparison")
MODULES.insert(MODULES.index("ShearSubstitution"), "SimpleFixedRootHessian")
MODULES.insert(MODULES.index("ShearSubstitution"), "ParametricSimpleFixedRoot")
MODULES.insert(MODULES.index("ShearSubstitution"), "SimpleRootLocalIntersection")
MODULES.insert(MODULES.index("ShearSubstitution"), "FiniteParameterGraphRuling")
MODULES.insert(MODULES.index("ShearSubstitution"), "RationalPointLocalModel")
MODULES.insert(MODULES.index("ShearSubstitution"), "DoubleLinePolynomialLocalModel")
MODULES.insert(MODULES.index("ShearSubstitution"), "DoubleLineLocalMultiplicity")
MODULES.insert(MODULES.index("ShearSubstitution"), "BinaryFirstOrderDivision")
MODULES.insert(MODULES.index("ShearSubstitution"), "SimplePolynomialLocalAlgebra")
MODULES.insert(MODULES.index("ShearSubstitution"), "SimplePolynomialIntersection")
MODULES.insert(MODULES.index("ShearSubstitution"), "HyperplaneSectionHilbertDegree")
MODULES.insert(MODULES.index("ShearSubstitution"), "RulingMixedDerivative")
MODULES.insert(MODULES.index("ShearSubstitution"), "FiniteRulingSimpleHessian")
MODULES.insert(MODULES.index("ShearSubstitution"), "QuadraticBoundaryChart")
MODULES.insert(MODULES.index("ShearSubstitution"), "ParametricModifiedQuadricJets")
MODULES.insert(MODULES.index("ShearSubstitution"), "RulingBoundaryBasis")
MODULES.insert(MODULES.index("ShearSubstitution"), "RankOneBoundaryChart")
MODULES.insert(MODULES.index("ShearSubstitution"), "FiniteGaussBoundaryLocalIntersection")
MODULES.insert(MODULES.index("ShearSubstitution"), "RationalPointLocalQuotient")
MODULES.insert(MODULES.index("ShearSubstitution"), "SimplePolynomialSubschemeLocalBound")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveInfinityChartLocalBound")
MODULES.insert(MODULES.index("ShearSubstitution"), "SpecifiedRulingDualCoordinates")
MODULES.insert(MODULES.index("ShearSubstitution"), "FiniteGaussBoundaryPoint")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveModifiedBoundaryEquation")
MODULES.insert(MODULES.index("ShearSubstitution"), "FiniteGaussActualBoundaryLocalBound")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveEmptyHilbertVanishing")
MODULES.insert(MODULES.index("ShearSubstitution"), "HomogeneousSectionMultiplication")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveDehomogenizedIdeal")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveOriginLocalHilbertBound")
MODULES.insert(MODULES.index("ShearSubstitution"), "SingleSupportHyperplaneDegree")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedProjectiveInfinityChart")
MODULES.insert(MODULES.index("ShearSubstitution"), "FiberBoundaryCoefficientExtension")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveBoundaryProjection")
MODULES.insert(MODULES.index("ShearSubstitution"), "ActualClosedGaussSimpleBoundaryChart")
MODULES.insert(MODULES.index("ShearSubstitution"), "OriginalMapSimpleRootLocalModel")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectivePrimeCoordinates")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveNormalizedPrimeCoordinates")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectivePrimeBaseExtension")
MODULES.insert(MODULES.index("ShearSubstitution"), "ActualInfinityPrimeAlgebraicity")
MODULES.insert(MODULES.index("ShearSubstitution"), "ParameterAlgebraicFieldExtension")
MODULES.insert(MODULES.index("ShearSubstitution"), "SpecifiedSimpleRootDirection")
MODULES.insert(MODULES.index("ShearSubstitution"), "FiniteRootBoundaryFieldExtension")
MODULES.insert(MODULES.index("ShearSubstitution"), "ActualUniformSimpleBoundaryDirection")
MODULES.insert(MODULES.index("ShearSubstitution"), "GraphBoundaryProportionality")
MODULES.insert(MODULES.index("ShearSubstitution"), "ActualSimpleRootInfinitySupport")
MODULES.insert(MODULES.index("ShearSubstitution"), "GradedSurjectiveHilbertTransport")
MODULES.insert(MODULES.index("ShearSubstitution"), "InfinityCoordinateElimination")

MODULES.insert(MODULES.index("ShearSubstitution"), "GradedProjectiveSupportTransport")

MODULES.insert(MODULES.index("ShearSubstitution"), "InvertibleInfinityChart")

MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveGraphIdealImage")

MODULES.insert(MODULES.index("ShearSubstitution"), "InfinityChartHilbertBound")

MODULES.insert(MODULES.index("ShearSubstitution"), "ReindexedInfinityGraph")

MODULES.insert(MODULES.index("ShearSubstitution"), "OriginalFiberInfinityChartDegree")

MODULES.insert(MODULES.index("ShearSubstitution"), "HomogeneousPrincipalHilbert")

MODULES.insert(MODULES.index("ShearSubstitution"), "AffinePrincipalCone")

MODULES.insert(MODULES.index("ShearSubstitution"), "CoordinateProjectionHilbert")

MODULES.insert(MODULES.index("ShearSubstitution"), "PlaneEquationDegreeBound")

MODULES.insert(MODULES.index("ShearSubstitution"), "AffineTwoCoordinateLine")

MODULES.insert(MODULES.index("ShearSubstitution"), "DegreeOneAffineLine")

MODULES.insert(MODULES.index("ShearSubstitution"), "ActualNonlinearFiberDegree")

MODULES.insert(MODULES.index("ShearSubstitution"), "AffineProjectionHilbert")
MODULES.insert(MODULES.index("ShearSubstitution"), "AffinePlaneGeneratorDegree")

MODULES.insert(MODULES.index("ShearSubstitution"), "BinaryQuadraticExpansion")

MODULES.insert(MODULES.index("ShearSubstitution"), "BinaryQuadraticShear")

MODULES.insert(MODULES.index("ShearSubstitution"), "QuadraticShearGraph")

MODULES.insert(MODULES.index("ShearSubstitution"), "ParabolaFromAffineSquare")

MODULES.insert(MODULES.index("ShearSubstitution"), "TwoConstantCovectorsLine")

MODULES.insert(MODULES.index("ShearSubstitution"), "RankOneQuadricParabola")

MODULES.insert(MODULES.index("ShearSubstitution"), "AffineGraphParabola")

MODULES.insert(MODULES.index("ShearSubstitution"), "ActualDevelopableParabola")

MODULES.insert(MODULES.index("ShearSubstitution"), "ParabolaCoordinateAlgebra")

MODULES.insert(MODULES.index("ShearSubstitution"), "NonzeroHyperplaneRadialDegree")

MODULES.insert(MODULES.index("ShearSubstitution"), "OriginalFiberRadialDegree")

MODULES.insert(MODULES.index("ShearSubstitution"), "OriginalClosureInfinitySupport")

MODULES.insert(MODULES.index("ShearSubstitution"), "ParabolaCoordinateUnits")

MODULES.insert(MODULES.index("ShearSubstitution"), "ParabolaPointNonvanishing")

MODULES.insert(MODULES.index("ShearSubstitution"), "ParabolaFieldEmbedding")

MODULES.insert(MODULES.index("ShearSubstitution"), "SelectedGeometricParabola")

MODULES.insert(MODULES.index("ShearSubstitution"), "CoprimeBaseGenericAvoidance")

MODULES.insert(MODULES.index("ShearSubstitution"), "GenericFiberCoprimeBase")

MODULES.insert(MODULES.index("ShearSubstitution"), "GeometricParameterCrossRelation")

MODULES.insert(MODULES.index("ShearSubstitution"), "GeometricParameterPencilConstants")

MODULES.insert(MODULES.index("ShearSubstitution"), "CompatibleParameterPolynomialRelation")

MODULES.insert(MODULES.index("ShearSubstitution"), "HomogeneousAffineLeadingCoefficient")

MODULES.insert(MODULES.index("ShearSubstitution"), "VertexPolynomialExpansion")

MODULES.insert(MODULES.index("ShearSubstitution"), "ParabolicVertexLeadingCoefficient")

MODULES.insert(MODULES.index("ShearSubstitution"), "TranscendentalPolynomialParametrization")

MODULES.insert(MODULES.index("ShearSubstitution"), "ActualParabolicVertexConstraint")

MODULES.insert(MODULES.index("ShearSubstitution"), "GeometricParameterVertexConstraint")

MODULES.insert(MODULES.index("ShearSubstitution"), "MovingPlaneLowestCoefficient")

MODULES.insert(MODULES.index("ShearSubstitution"), "MovingPlaneBinaryRestriction")

MODULES.insert(MODULES.index("ShearSubstitution"), "MovingPlanePointAlgebraicity")

MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryMovingLineAlgebraicity")

MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveCovectorTranscendence")

MODULES.insert(MODULES.index("ShearSubstitution"), "NonconstantTangentLineAlgebraicity")

MODULES.insert(MODULES.index("ShearSubstitution"), "GeometricParameterDirectionAlgebraicity")

MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveRatioEmbedding")

MODULES.insert(MODULES.index("ShearSubstitution"), "ConeNormalGaussField")

MODULES.insert(MODULES.index("ShearSubstitution"), "ConstantProjectedDirectionPlane")

MODULES.insert(MODULES.index("ShearSubstitution"), "GeometricConstantProjectedDirection")

MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectedDirectionCurveDimension")

MODULES.insert(MODULES.index("ShearSubstitution"), "GeometricProjectedDirectionCurve")

MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectedDirectionDependenceDescent")

MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectivePointChartIdeal")

MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryProjectivePointPrincipal")

MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectivePointEquationRegularity")

MODULES.insert(MODULES.index("ShearSubstitution"), "GeometricProjectedDirectionEquation")

MODULES.insert(MODULES.index("ShearSubstitution"), "HomogeneousAffineReflection")

MODULES.insert(MODULES.index("ShearSubstitution"), "HomogeneousAffineTangentCoefficient")

MODULES.insert(MODULES.index("ShearSubstitution"), "DirectionEquationMultiplicity")

MODULES.insert(MODULES.index("ShearSubstitution"), "DirectionMultiplicityLeadingTerm")

MODULES.insert(MODULES.index("ShearSubstitution"), "GenericDirectionTangent")

MODULES.insert(MODULES.index("ShearSubstitution"), "DirectionFieldLeadingCoefficient")

MODULES.insert(MODULES.index("ShearSubstitution"), "ParabolicMaximalCoefficient")

MODULES.insert(MODULES.index("ShearSubstitution"), "TangentScaledPolynomialRelation")

MODULES.insert(MODULES.index("ShearSubstitution"), "OriginalParabolicCoefficientFamily")

MODULES.insert(MODULES.index("ShearSubstitution"), "ParabolicCoefficientAlgebraicity")

MODULES.insert(MODULES.index("ShearSubstitution"), "OriginalInvariantTangentConstraint")

MODULES.insert(MODULES.index("ShearSubstitution"), "FiniteTangentProportionality")

MODULES.insert(MODULES.index("ShearSubstitution"), "GenericFiberTangentNonvanishing")

MODULES.insert(MODULES.index("ShearSubstitution"), "ActualParabolaTangentConstraint")

MODULES.insert(MODULES.index("ShearSubstitution"), "GeometricParameterTangentProportionality")

MODULES.insert(MODULES.index("ShearSubstitution"), "RulingFiniteTangentField")

MODULES.insert(MODULES.index("ShearSubstitution"), "ReducedPencilVertexDifferential")

MODULES.insert(MODULES.index("ShearSubstitution"), "VertexParameterTranscendence")

MODULES.insert(MODULES.index("ShearSubstitution"), "TransverseParameterIndependence")

MODULES.insert(MODULES.index("ShearSubstitution"), "ClosedGaussTransverseIndependence")

MODULES.insert(MODULES.index("ShearSubstitution"), "ConstantFieldFactorization")

MODULES.insert(MODULES.index("ShearSubstitution"), "RealizedFieldIndependence")

MODULES.insert(MODULES.index("ShearSubstitution"), "GeometricClosedGaussEmbedding")

MODULES.insert(MODULES.index("ShearSubstitution"), "GeometricAlgebraicSourceIndependence")

MODULES.insert(MODULES.index("ShearSubstitution"), "GeometricBranchTangentProportionality")

MODULES.insert(MODULES.index("ShearSubstitution"), "CommonFiniteDirectionTangentField")

MODULES.insert(MODULES.index("ShearSubstitution"), "GeometricNormalizedTangentField")

MODULES.insert(MODULES.index("ShearSubstitution"), "TensorPolynomialDescent")

MODULES.insert(MODULES.index("ShearSubstitution"), "ClosedGaussCoefficientDescent")

MODULES.insert(MODULES.index("ShearSubstitution"), "RationalGaussCoefficientDescent")

MODULES.insert(MODULES.index("ShearSubstitution"), "ConeTernaryForms")

MODULES.insert(MODULES.index("ShearSubstitution"), "TangentMultipleSourceValue")

MODULES.insert(MODULES.index("ShearSubstitution"), "ActualConeTernaryExpansion")

MODULES.insert(MODULES.index("ShearSubstitution"), "RealizedPolynomialDescent")

MODULES.insert(MODULES.index("ShearSubstitution"), "RealizedGaussTernaryDescent")

MODULES.insert(MODULES.index("ShearSubstitution"), "RealizedConeParameterForms")

MODULES.insert(MODULES.index("ShearSubstitution"), "FiniteCoefficientFieldEnlargement")

MODULES.insert(MODULES.index("ShearSubstitution"), "GeometricConeParameterConstruction")

MODULES.insert(MODULES.index("ShearSubstitution"), "PolePullbackIntegrality")

MODULES.insert(MODULES.index("ShearSubstitution"), "PolynomialPolePullback")

MODULES.insert(MODULES.index("ShearSubstitution"), "PrimitiveParameterDenominator")

MODULES.insert(MODULES.index("ShearSubstitution"), "GenericParameterPole")

MODULES.insert(MODULES.index("ShearSubstitution"), "PolynomialParameterRegularity")

MODULES.insert(MODULES.index("ShearSubstitution"), "ActualVertexPolynomialChart")

MODULES.insert(MODULES.index("ShearSubstitution"), "ActualGaussParameterPoles")

MODULES.insert(MODULES.index("ShearSubstitution"), "PolynomialParameterChange")

MODULES.insert(MODULES.index("ShearSubstitution"), "GaussVertexOutputDependence")

MODULES.insert(MODULES.index("ShearSubstitution"), "ActualGaussPolynomialParameter")

MODULES.insert(MODULES.index("ShearSubstitution"), "GeometricConePolynomialParameter")

MODULES.insert(MODULES.index("ShearSubstitution"), "ConstantReciprocalParameterEquiv")

MODULES.insert(MODULES.index("ShearSubstitution"), "TransverseSourceFractionField")

MODULES.insert(MODULES.index("ShearSubstitution"), "VertexPolynomialCoefficientClearing")

MODULES.insert(MODULES.index("ShearSubstitution"), "PolynomialGaussCoverParameter")

MODULES.insert(MODULES.index("ShearSubstitution"), "VertexIndependentReducedDenominator")

MODULES.insert(MODULES.index("ShearSubstitution"), "PolynomialParameterFormCoefficients")

MODULES.insert(MODULES.index("ShearSubstitution"), "ActualPolynomialGaussForms")

MODULES.insert(MODULES.index("ShearSubstitution"), "GeometricConePolynomialForms")

MODULES.insert(MODULES.index("ShearSubstitution"), "LinearPowerCoefficientDescent")

MODULES.insert(MODULES.index("ShearSubstitution"), "PrimitiveParameterLinearForm")

MODULES.insert(MODULES.index("ShearSubstitution"), "PrimitiveParameterScalarGauss")

MODULES.insert(MODULES.index("ShearSubstitution"), "PrimitivePolynomialLinearPowerFamily")

MODULES.insert(MODULES.index("ShearSubstitution"), "ConeLinearFactorDescent")

MODULES.insert(MODULES.index("ShearSubstitution"), "RealizedConeLinearFactor")

MODULES.insert(MODULES.index("ShearSubstitution"), "GeometricConeRationalLinearFactor")

MODULES.insert(MODULES.index("ShearSubstitution"), "ActualPrimitiveConeForms")

MODULES.insert(MODULES.index("ShearSubstitution"), "GeometricPrimitiveConeForms")

MODULES.insert(MODULES.index("ShearSubstitution"), "PolynomialScalarFactorRegularity")

MODULES.insert(MODULES.index("ShearSubstitution"), "ParameterLinearSourceValue")

MODULES.insert(MODULES.index("ShearSubstitution"), "PolynomialScalarDenominatorDivisibility")

MODULES.insert(MODULES.index("ShearSubstitution"), "SourceEulerLinearFactor")

MODULES.insert(MODULES.index("ShearSubstitution"), "LinearSourceDenominatorPower")

MODULES.insert(MODULES.index("ShearSubstitution"), "GaussLinearCoefficientRigidity")

MODULES.insert(MODULES.index("ShearSubstitution"), "ActualFixedConeLinearForm")

MODULES.insert(MODULES.index("ShearSubstitution"), "GeometricFixedConeLinearForm")

MODULES.insert(MODULES.index("ShearSubstitution"), "LinearPowerQuotientRecovery")

MODULES.insert(MODULES.index("ShearSubstitution"), "LinearPowerFactorUniqueness")

MODULES.insert(MODULES.index("ShearSubstitution"), "CompleteConeLinearFactorDescent")

MODULES.insert(MODULES.index("ShearSubstitution"), "FixedLinearPowerPolynomialQuotient")

MODULES.insert(MODULES.index("ShearSubstitution"), "RealizedCompleteConeFactorization")

MODULES.insert(MODULES.index("ShearSubstitution"), "GeometricCompleteRationalConeForms")

MODULES.insert(MODULES.index("ShearSubstitution"), "ActualCompleteFixedConeForms")
MODULES.insert(MODULES.index("ShearSubstitution"), "GeometricCompleteFixedConeForms")
MODULES.insert(MODULES.index("ShearSubstitution"), "LinearPolynomialConjugacy")
MODULES.insert(MODULES.index("ShearSubstitution"), "FixedCovectorCoordinateChoice")
MODULES.insert(MODULES.index("ShearSubstitution"), "FixedConeCoordinateConjugacy")
MODULES.insert(MODULES.index("ShearSubstitution"), "FixedConeAffineParameter")
MODULES.insert(MODULES.index("ShearSubstitution"), "GeometricCoordinateConeForms")
MODULES.insert(MODULES.index("ShearSubstitution"), "LinearConjugacyRank")
MODULES.insert(MODULES.index("ShearSubstitution"), "SecondCoordinateAffineChart")
MODULES.insert(MODULES.index("ShearSubstitution"), "AffineConePolynomialForms")
MODULES.insert(MODULES.index("ShearSubstitution"), "AffineConeTrace")
MODULES.insert(MODULES.index("ShearSubstitution"), "GeometricAffineConeTrace")
MODULES.insert(MODULES.index("ShearSubstitution"), "NilpotentConstantConeCoordinate")
MODULES.insert(MODULES.index("ShearSubstitution"), "QuadraticConeLevelSubstitution")
MODULES.insert(MODULES.index("ShearSubstitution"), "QuadraticEulerComparison")
MODULES.insert(MODULES.index("ShearSubstitution"), "QuadraticConeTraceExclusion")
MODULES.insert(MODULES.index("ShearSubstitution"), "GeometricQuadraticConeObstruction")
MODULES.insert(MODULES.index("ShearSubstitution"), "VertexPreservingSourcePartial")
MODULES.insert(MODULES.index("ShearSubstitution"), "ChangedGaussVertexDifferential")
MODULES.insert(MODULES.index("ShearSubstitution"), "AffineConeVertexDifferential")
MODULES.insert(MODULES.index("ShearSubstitution"), "GeometricAffineVertexDifferential")
MODULES.insert(MODULES.index("ShearSubstitution"), "AffineTangentCommutator")
MODULES.insert(MODULES.index("ShearSubstitution"), "AffineTangentQuadraticPotential")
MODULES.insert(MODULES.index("ShearSubstitution"), "CommutativePolynomialChainRule")
MODULES.insert(MODULES.index("ShearSubstitution"), "AffineQuadraticShearInvariants")
MODULES.insert(MODULES.index("ShearSubstitution"), "AffineTangentNormalization")
MODULES.insert(MODULES.index("ShearSubstitution"), "IndependentAffineTangentParameter")
MODULES.insert(MODULES.index("ShearSubstitution"), "GeometricAffineTangentParameter")
MODULES.insert(MODULES.index("ShearSubstitution"), "RelativeClosureCoordinateTransport")
MODULES.insert(MODULES.index("ShearSubstitution"), "PrimitivePolynomialParameterDegree")
MODULES.insert(MODULES.index("ShearSubstitution"), "ActualPrimitiveAffineParameter")
MODULES.insert(MODULES.index("ShearSubstitution"), "GeometricPrimitiveAffineParameter")
MODULES.insert(MODULES.index("ShearSubstitution"), "GenericAffineLevelKernel")
MODULES.insert(MODULES.index("ShearSubstitution"), "AffineLevelParameterField")
MODULES.insert(MODULES.index("ShearSubstitution"), "AffineLevelGeometricIntegrality")
MODULES.insert(MODULES.index("ShearSubstitution"), "GeometricAffineLevelIntegrality")
MODULES.insert(MODULES.index("ShearSubstitution"), "AffineTriangularFlow")
MODULES.insert(MODULES.index("ShearSubstitution"), "AffineTriangularDivisibility")
MODULES.insert(MODULES.index("ShearSubstitution"), "ActualAffineLevelTangent")
MODULES.insert(MODULES.index("ShearSubstitution"), "ConjugatedGaussAffineLevelTangent")
MODULES.insert(MODULES.index("ShearSubstitution"), "AffineTangentCoefficientDescent")
MODULES.insert(MODULES.index("ShearSubstitution"), "ActualGaussGenericTangentGraph")
MODULES.insert(MODULES.index("ShearSubstitution"), "ConeRankOneTraceElimination")
MODULES.insert(MODULES.index("ShearSubstitution"), "AffineConeJacobianMatrix")
MODULES.insert(MODULES.index("ShearSubstitution"), "ConeWronskianHorizontalIndependence")
MODULES.insert(MODULES.index("ShearSubstitution"), "ConstructedConeTangentPolynomials")
MODULES.insert(MODULES.index("ShearSubstitution"), "ActualConeTangentConstruction")
MODULES.insert(MODULES.index("ShearSubstitution"), "AffineParameterParabolaObstruction")
MODULES.insert(MODULES.index("ShearSubstitution"), "VertexPreservingParabolaTransport")
MODULES.insert(MODULES.index("ShearSubstitution"), "ConjugatedAffineParabolaObstruction")
MODULES.insert(MODULES.index("ShearSubstitution"), "GeometricFixedConeExclusion")
MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryRulingDirection")
MODULES.insert(MODULES.index("ShearSubstitution"), "OriginalConeScalarDirection")
MODULES.insert(MODULES.index("ShearSubstitution"), "ClosedConeScalarDirection")
MODULES.insert(MODULES.index("ShearSubstitution"), "GeometricConeScalarRoot")
MODULES.insert(MODULES.index("ShearSubstitution"), "RealizedConeNormalIncidence")
MODULES.insert(MODULES.index("ShearSubstitution"), "RealizedConeMovingNormal")
MODULES.insert(MODULES.index("ShearSubstitution"), "GeometricConeMovingNormal")
MODULES.insert(MODULES.index("ShearSubstitution"), "FixedVertexCharacteristicAxis")
MODULES.insert(MODULES.index("ShearSubstitution"), "NativeFixedVertexConeForm")
MODULES.insert(MODULES.index("ShearSubstitution"), "HomogeneousConeFormulaTransfer")
MODULES.insert(MODULES.index("ShearSubstitution"), "AffineSourceConeForm")
MODULES.insert(MODULES.index("ShearSubstitution"), "HomogeneousRationalRootTransfer")
MODULES.insert(MODULES.index("ShearSubstitution"), "AffineFixedVertexRootAlternatives")
MODULES.insert(MODULES.index("ShearSubstitution"), "OriginalFixedVertexAffineRootCases")
MODULES.insert(MODULES.index("ShearSubstitution"), "AlgebraicSourceTensorRealization")
MODULES.insert(MODULES.index("ShearSubstitution"), "CompatibleAlgebraicSourceRealization")
MODULES.insert(MODULES.index("ShearSubstitution"), "ClosedGaussAlgebraicRealization")
MODULES.insert(MODULES.index("ShearSubstitution"), "RealizedAffineConeRootCases")
MODULES.insert(MODULES.index("ShearSubstitution"), "FiniteAffineRootCaseRealization")
MODULES.insert(MODULES.index("ShearSubstitution"), "GeometricFixedVertexRootCases")
MODULES.insert(MODULES.index("ShearSubstitution"), "RankOneUpdateTrace")
MODULES.insert(MODULES.index("ShearSubstitution"), "ConeParameterJacobianSlope")
MODULES.insert(MODULES.index("ShearSubstitution"), "VertexParameterDerivationFrame")
MODULES.insert(MODULES.index("ShearSubstitution"), "VertexFrameConeJacobian")
MODULES.insert(MODULES.index("ShearSubstitution"), "ConeRootSlopeIdentity")
MODULES.insert(MODULES.index("ShearSubstitution"), "RationalParameterAlgebraicDerivative")
MODULES.insert(MODULES.index("ShearSubstitution"), "ConeQuadraticCoefficient")
MODULES.insert(MODULES.index("ShearSubstitution"), "ConstructedConeRootSlope")
MODULES.insert(MODULES.index("ShearSubstitution"), "AlgebraicSourceTensorPartials")
MODULES.insert(MODULES.index("ShearSubstitution"), "ConeQuadraticRootNormalization")
MODULES.insert(MODULES.index("ShearSubstitution"), "AlgebraicSourceDerivationChain")
MODULES.insert(MODULES.index("ShearSubstitution"), "ComponentSourceAlgebraicity")
MODULES.insert(MODULES.index("ShearSubstitution"), "ParabolicFiberDerivation")
MODULES.insert(MODULES.index("ShearSubstitution"), "GeometricAlgebraicSourceEmbedding")
MODULES.insert(MODULES.index("ShearSubstitution"), "ActualFiberSourceFrame")
MODULES.insert(MODULES.index("ShearSubstitution"), "ParameterDirectionAlgebraicity")
MODULES.insert(MODULES.index("ShearSubstitution"), "ActualParabolicConeSlope")
MODULES.insert(MODULES.index("ShearSubstitution"), "GeometricAlgebraicRootCases")
MODULES.insert(MODULES.index("ShearSubstitution"), "GeometricQuadraticRootNormalization")
MODULES.insert(MODULES.index("ShearSubstitution"), "CompatibleGeometricParameterFrame")
MODULES.insert(MODULES.index("ShearSubstitution"), "GeometricOriginalSourcePartials")
MODULES.insert(MODULES.index("ShearSubstitution"), "RankThreeDerivationKernel")
MODULES.insert(MODULES.index("ShearSubstitution"), "ConeDirectrixDerivativeNonzero")
MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryTangentDecomposition")
MODULES.insert(MODULES.index("ShearSubstitution"), "NormalJetTangentDecomposition")
MODULES.insert(MODULES.index("ShearSubstitution"), "RankThreeActualParabolicCone")
MODULES.insert(MODULES.index("ShearSubstitution"), "RationalJetMinorTransfer")
MODULES.insert(MODULES.index("ShearSubstitution"), "ClosedGaussNormalJetRealization")
MODULES.insert(MODULES.index("ShearSubstitution"), "ClosedConeSourceIncidences")
MODULES.insert(MODULES.index("ShearSubstitution"), "ParameterAlgebraicFieldReflection")
MODULES.insert(MODULES.index("ShearSubstitution"), "ActualClosedConeQuadraticCoefficient")
MODULES.insert(MODULES.index("ShearSubstitution"), "TransverseFrameCommutation")
MODULES.insert(MODULES.index("ShearSubstitution"), "SquareZeroRankOneKernel")
MODULES.insert(MODULES.index("ShearSubstitution"), "ConstantKernelAcceleration")
MODULES.insert(MODULES.index("ShearSubstitution"), "ConeSquareZeroBlock")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProportionalConeKernelDirection")
MODULES.insert(MODULES.index("ShearSubstitution"), "ActualProportionalConeExclusion")
MODULES.insert(MODULES.index("ShearSubstitution"), "NonlinearClosedConeQuadraticCoefficient")
MODULES.insert(MODULES.index("ShearSubstitution"), "ParabolaDirectionNormalization")
MODULES.insert(MODULES.index("ShearSubstitution"), "NormalizedClosedConeQuadraticCoefficient")
MODULES.insert(MODULES.index("ShearSubstitution"), "GeometricConeQuadraticCoefficient")
MODULES.insert(MODULES.index("ShearSubstitution"), "CompatibleGeometricSource")
MODULES.insert(MODULES.index("ShearSubstitution"), "GeometricConstructedConeExclusion")
MODULES.insert(MODULES.index("ShearSubstitution"), "NonlinearProjectedDirection")
MODULES.insert(MODULES.index("ShearSubstitution"), "GeometricScaledPlaneReduction")
MODULES.insert(MODULES.index("ShearSubstitution"), "ZeroPoleLocalReciprocal")
MODULES.insert(MODULES.index("ShearSubstitution"), "ZeroPoleLevelValuation")
MODULES.insert(MODULES.index("ShearSubstitution"), "FractionDenominatorIdeal")
MODULES.insert(MODULES.index("ShearSubstitution"), "NormalFractionPolePrime")
MODULES.insert(MODULES.index("ShearSubstitution"), "NormalCodimensionOneRegularity")
MODULES.insert(MODULES.index("ShearSubstitution"), "NormalHeightOneLevel")
MODULES.insert(MODULES.index("ShearSubstitution"), "ZeroPoleLevelClosure")
MODULES.insert(MODULES.index("ShearSubstitution"), "GeneralRationalLevelDivisors")
MODULES.insert(MODULES.index("ShearSubstitution"), "ZeroPoleGeneralLevelClosure")
MODULES.insert(MODULES.index("ShearSubstitution"), "NormalBranchGeneralLevelClosure")
MODULES.insert(MODULES.index("ShearSubstitution"), "FixedVertexRootNumerator")
MODULES.insert(MODULES.index("ShearSubstitution"), "PencilBaseNormalKernel")
MODULES.insert(MODULES.index("ShearSubstitution"), "FixedVertexPencilBase")
MODULES.insert(MODULES.index("ShearSubstitution"), "AffinePencilBaseRelations")
MODULES.insert(MODULES.index("ShearSubstitution"), "ScaledPlaneBasePower")
MODULES.insert(MODULES.index("ShearSubstitution"), "FixedVertexNumeratorBaseZero")
MODULES.insert(MODULES.index("ShearSubstitution"), "PencilBaseZeroBranch")
MODULES.insert(MODULES.index("ShearSubstitution"), "AlgebraicPolynomialDescent")
MODULES.insert(MODULES.index("ShearSubstitution"), "PolynomialCovectorProjectiveDescent")
MODULES.insert(MODULES.index("ShearSubstitution"), "IndependentParameterPolynomialDescent")
MODULES.insert(MODULES.index("ShearSubstitution"), "ScaledNormalPowerDirection")
MODULES.insert(MODULES.index("ShearSubstitution"), "IndependentGaussCoefficientRealization")
MODULES.insert(MODULES.index("ShearSubstitution"), "ScaledPlaneBaseProjection")
MODULES.insert(MODULES.index("ShearSubstitution"), "ScaledPlaneBasePrimeLine")
MODULES.insert(MODULES.index("ShearSubstitution"), "VertexLineContainment")
MODULES.insert(MODULES.index("ShearSubstitution"), "VertexLinePrime")
MODULES.insert(MODULES.index("ShearSubstitution"), "VertexLinePrimeIdentification")
MODULES.insert(MODULES.index("ShearSubstitution"), "ScaledPlaneBaseComponents")
MODULES.insert(MODULES.index("ShearSubstitution"), "HomogeneousPencilBaseExistence")
MODULES.insert(MODULES.index("ShearSubstitution"), "VertexLineIncidence")
MODULES.insert(MODULES.index("ShearSubstitution"), "ClosedGaussVertexLineIncidence")
MODULES.insert(MODULES.index("ShearSubstitution"), "VertexLineCoefficientExtension")
MODULES.insert(MODULES.index("ShearSubstitution"), "ScaledPlaneBaseVertexIntersection")
MODULES.insert(MODULES.index("ShearSubstitution"), "DegreePreservingPolynomialKernel")
MODULES.insert(MODULES.index("ShearSubstitution"), "IntegralNormalizationPointLifting")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveVertexLine")
MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedPencilVertexLineLift")
MODULES.insert(MODULES.index("ShearSubstitution"), "ScaledPlaneNormalizedBaseBranch")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveVertexLineNormalSection")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectivePolynomialGermVanishing")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectivePolynomialQuotientGerm")
MODULES.insert(MODULES.index("ShearSubstitution"), "ScaledPlaneNormalizedZeroGerm")
MODULES.insert(MODULES.index("ShearSubstitution"), "SeparatingZeroDivisors")
MODULES.insert(MODULES.index("ShearSubstitution"), "SpecializationGermDivisors")
MODULES.insert(MODULES.index("ShearSubstitution"), "NativePolynomialGermPointEquations")
MODULES.insert(MODULES.index("ShearSubstitution"), "ScaledPlaneLocalHeightOneBranches")
MODULES.insert(MODULES.index("ShearSubstitution"), "RegularQuotientIdealPowers")
MODULES.insert(MODULES.index("ShearSubstitution"), "NativePolynomialGermHom")
MODULES.insert(MODULES.index("ShearSubstitution"), "NativeScaledPlanePoleCriterion")
MODULES.insert(MODULES.index("ShearSubstitution"), "FixedVertexScaledOutputSpan")
MODULES.insert(MODULES.index("ShearSubstitution"), "FixedVertexScaledPlanePoles")
MODULES.insert(MODULES.index("ShearSubstitution"), "LocalZeroPoleCriterion")
MODULES.insert(MODULES.index("ShearSubstitution"), "ActualNormalPlaneDivisorPoles")
MODULES.insert(MODULES.index("ShearSubstitution"), "IteratedPrimeLocalizationRegularity")
MODULES.insert(MODULES.index("ShearSubstitution"), "ActualNormalizedChartPointPrimes")
MODULES.insert(MODULES.index("ShearSubstitution"), "AffineStalkPrimeRegularity")

MODULES.insert(MODULES.index("ShearSubstitution"), "ActualVertexStalkDenominatorPoles")

MODULES.insert(MODULES.index("ShearSubstitution"), "ScaledPlaneVertexGeneralLevels")

MODULES.insert(MODULES.index("ShearSubstitution"), "AffineStalkLevelClosure")

MODULES.insert(MODULES.index("ShearSubstitution"), "NativeProjectiveLevelClosure")

MODULES.insert(MODULES.index("ShearSubstitution"), "ScaledPlaneVertexProjectiveLevels")

MODULES.insert(MODULES.index("ShearSubstitution"), "FixedVertexScaledDualOutputBasis")

MODULES.insert(MODULES.index("ShearSubstitution"), "ScaledPlaneLevelTargetEquations")

MODULES.insert(MODULES.index("ShearSubstitution"), "ScaledPlaneVertexTargetFibers")

MODULES.insert(MODULES.index("ShearSubstitution"), "LinearHyperplaneProjectiveGraph")

MODULES.insert(MODULES.index("ShearSubstitution"), "LinearHyperplaneGraphPoints")

MODULES.insert(MODULES.index("ShearSubstitution"), "HyperplaneAffineFiberLocus")

MODULES.insert(MODULES.index("ShearSubstitution"), "ScaledPlaneVertexAffineFiberBoundary")

MODULES.insert(MODULES.index("ShearSubstitution"), "LocallyClosedSpecialization")

MODULES.insert(MODULES.index("ShearSubstitution"), "HyperplaneAffineFiberBranch")

MODULES.insert(MODULES.index("ShearSubstitution"), "ScaledPlaneAffineBranchBoundary")

MODULES.insert(MODULES.index("ShearSubstitution"), "IntegralLevelReciprocal")

MODULES.insert(MODULES.index("ShearSubstitution"), "NormalGraphResidueKernel")

MODULES.insert(MODULES.index("ShearSubstitution"), "RationalGraphResidueAlgebra")

MODULES.insert(MODULES.index("ShearSubstitution"), "RationalGraphGenericParameter")

MODULES.insert(MODULES.index("ShearSubstitution"), "RationalGraphLocalParameter")

MODULES.insert(MODULES.index("ShearSubstitution"), "ScaledPlaneVertexGenericGraph")

MODULES.insert(MODULES.index("ShearSubstitution"), "GenericGraphProjectiveBoundary")

MODULES.insert(MODULES.index("ShearSubstitution"), "NativeVertexGermCoordinates")

MODULES.insert(MODULES.index("ShearSubstitution"), "GenericGraphVertexInfinity")

MODULES.insert(MODULES.index("ShearSubstitution"), "ScaledPlaneGenericLevelBoundary")

MODULES.insert(MODULES.index("ShearSubstitution"), "ScaledPlaneGenericTargetFiber")

MODULES.insert(MODULES.index("ShearSubstitution"), "RationalScalarLocalization")

MODULES.insert(MODULES.index("ShearSubstitution"), "RationalScalarBoundary")

MODULES.insert(MODULES.index("ShearSubstitution"), "RationalScalarVertexInfinity")

MODULES.insert(MODULES.index("ShearSubstitution"), "GenericGraphScaledVertexInfinity")

MODULES.insert(MODULES.index("ShearSubstitution"), "IndependentScaleHomogeneousValues")

MODULES.insert(MODULES.index("ShearSubstitution"), "ScaledPlaneIndependentScaleBoundary")

MODULES.insert(MODULES.index("ShearSubstitution"), "IndependentScaleSourceEmbedding")

MODULES.insert(MODULES.index("ShearSubstitution"), "NativeOriginalSourceFaithfulness")

MODULES.insert(MODULES.index("ShearSubstitution"), "NativeIndependentScaleSource")

MODULES.insert(MODULES.index("ShearSubstitution"), "NativeScaleHomogeneousQuotients")

MODULES.insert(MODULES.index("ShearSubstitution"), "NativeScaleClosedGaussCoefficients")

MODULES.insert(MODULES.index("ShearSubstitution"), "CompatibleFullOutputEmbedding")

MODULES.insert(MODULES.index("ShearSubstitution"), "AlgebraicConstantsCompatibleImages")

MODULES.insert(MODULES.index("ShearSubstitution"), "NativeScaleAlgebraicCoefficients")

MODULES.insert(MODULES.index("ShearSubstitution"), "AlgebraicRationalFunctionImages")

MODULES.insert(MODULES.index("ShearSubstitution"), "ScaledRulingParameterAlgebraicity")

MODULES.insert(MODULES.index("ShearSubstitution"), "NativeScaledFullOutputEmbedding")

MODULES.insert(MODULES.index("ShearSubstitution"), "ScaledPlaneAlgebraicFullOutputBoundary")

MODULES.insert(MODULES.index("ShearSubstitution"), "AlgebraicCompatibleSourceComponent")

MODULES.insert(MODULES.index("ShearSubstitution"), "HomogeneousCoefficientComponents")

MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveBoundaryCoefficientComponent")

MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveChartComponentRelations")

MODULES.insert(MODULES.index("ShearSubstitution"), "AlgebraicComponentTower")

MODULES.insert(MODULES.index("ShearSubstitution"), "ScaledPlaneGeometricFullOutputBoundary")

MODULES.insert(MODULES.index("ShearSubstitution"), "ComponentSourceRealizationTransport")

MODULES.insert(MODULES.index("ShearSubstitution"), "CoefficientCompatibleComponentSource")

MODULES.insert(MODULES.index("ShearSubstitution"), "NativeGeometricClosedCoefficients")

MODULES.insert(MODULES.index("ShearSubstitution"), "OriginalAffineTensorRealization")

MODULES.insert(MODULES.index("ShearSubstitution"), "NativeGeometricAffineTensor")

MODULES.insert(MODULES.index("ShearSubstitution"), "ScaledPlaneGeometricTensorComponent")

MODULES.insert(MODULES.index("ShearSubstitution"), "SpecifiedAffineRootEquations")

MODULES.insert(MODULES.index("ShearSubstitution"), "ComponentOriginalOutputValues")

MODULES.insert(MODULES.index("ShearSubstitution"), "GeometricComponentSpecifiedRoots")

MODULES.insert(MODULES.index("ShearSubstitution"), "ScaledPlaneGeometricRootComponent")

MODULES.insert(MODULES.index("ShearSubstitution"), "GraphRulingCovectorProjection")

MODULES.insert(MODULES.index("ShearSubstitution"), "ActualChosenGraphDualPair")

MODULES.insert(MODULES.index("ShearSubstitution"), "SpecifiedGraphDualTransport")

MODULES.insert(MODULES.index("ShearSubstitution"), "SameComponentGraphCoefficients")

MODULES.insert(MODULES.index("ShearSubstitution"), "CompatibleSourceBoundaryTransport")

MODULES.insert(MODULES.index("ShearSubstitution"), "ActualSpecifiedSimpleRootBoundary")

MODULES.insert(MODULES.index("ShearSubstitution"), "NativeGeometricGraphCoefficients")

MODULES.insert(MODULES.index("ShearSubstitution"), "CanonicalGraphRootFactor")

MODULES.insert(MODULES.index("ShearSubstitution"), "AlgebraicSourceConstantLift")

MODULES.insert(MODULES.index("ShearSubstitution"), "SpecifiedTensorFirstInvariant")

MODULES.insert(MODULES.index("ShearSubstitution"), "SpecifiedGraphOutputValues")

MODULES.insert(MODULES.index("ShearSubstitution"), "SpecifiedGraphCoefficientExtension")

MODULES.insert(MODULES.index("ShearSubstitution"), "ScaledPlaneOriginalGraphBoundary")

MODULES.insert(MODULES.index("ShearSubstitution"), "CanonicalScaledPlaneBoundaryContradiction")

MODULES.insert(MODULES.index("ShearSubstitution"), "ScaledPlaneOriginalPowerData")

MODULES.insert(MODULES.index("ShearSubstitution"), "ActualGaussRootFullCone")

MODULES.insert(MODULES.index("ShearSubstitution"), "OriginalMapFullAffineCone")

MODULES.insert(MODULES.index("ShearSubstitution"), "RealizedAffineFullCone")

MODULES.insert(MODULES.index("ShearSubstitution"), "FiniteFullConeRealization")

MODULES.insert(MODULES.index("ShearSubstitution"), "GeometricFullConeRealization")

MODULES.insert(MODULES.index("ShearSubstitution"), "VertexParabolaGeometry")

MODULES.insert(MODULES.index("ShearSubstitution"), "OriginalVertexParabolaExclusion")

MODULES.insert(MODULES.index("ShearSubstitution"), "RadialCoordinateFieldDimension")

MODULES.insert(MODULES.index("ShearSubstitution"), "CoprimeTernaryProjectiveBase")

MODULES.insert(MODULES.index("ShearSubstitution"), "TransverseHomogeneousPencil")

MODULES.insert(MODULES.index("ShearSubstitution"), "OriginalVertexParabolaImpossible")

MODULES.insert(MODULES.index("ShearSubstitution"), "ParabolaInfinityDirection")

MODULES.insert(MODULES.index("ShearSubstitution"), "HomogeneousPolynomialLeadingCoefficient")

MODULES.insert(MODULES.index("ShearSubstitution"), "PolynomialCurveInfinity")

MODULES.insert(MODULES.index("ShearSubstitution"), "VertexParabolaFromInfinity")

MODULES.insert(MODULES.index("ShearSubstitution"), "OriginalParabolaVertexInfinityExclusion")

MODULES.insert(MODULES.index("ShearSubstitution"), "ParabolaInfinitySupport")

MODULES.insert(MODULES.index("ShearSubstitution"), "RealizedFullConeLevel")

MODULES.insert(MODULES.index("ShearSubstitution"), "FullConeIndependentRootForms")

MODULES.insert(MODULES.index("ShearSubstitution"), "ExtendedFullConeRootForms")

MODULES.insert(MODULES.index("ShearSubstitution"), "AffineFullConeIndependentRootData")

MODULES.insert(MODULES.index("ShearSubstitution"), "ActualGaussIndependentConeRootData")

MODULES.insert(MODULES.index("ShearSubstitution"), "OriginalMapIndependentConeRootData")

MODULES.insert(MODULES.index("ShearSubstitution"), "SourceTensorBoundaryRootTransfer")

MODULES.insert(MODULES.index("ShearSubstitution"), "FixedVertexIndependentGraphBasis")

MODULES.insert(MODULES.index("ShearSubstitution"), "BoundaryIndependentConeRootData")

MODULES.insert(MODULES.index("ShearSubstitution"), "BoundaryCanonicalIndependentRootData")

MODULES.insert(MODULES.index("ShearSubstitution"), "OriginalGraphTensorValues")

MODULES.insert(MODULES.index("ShearSubstitution"), "OriginalGraphBoundaryValues")

MODULES.insert(MODULES.index("ShearSubstitution"), "NativeIndependentRootGraphTransfer")

MODULES.insert(MODULES.index("ShearSubstitution"), "OriginalMapIndependentGraphRootData")

MODULES.insert(MODULES.index("ShearSubstitution"), "FiniteAlgebraicGraphDualPair")

MODULES.insert(MODULES.index("ShearSubstitution"), "FixedVertexFiniteGraphBasis")

MODULES.insert(MODULES.index("ShearSubstitution"), "FixedVertexGraphBasisWitness")

MODULES.insert(MODULES.index("ShearSubstitution"), "FiniteGraphRootActualDegree")

MODULES.insert(MODULES.index("ShearSubstitution"), "FixedVertexFiniteGraphBasisData")

MODULES.insert(MODULES.index("ShearSubstitution"), "FixedVertexGraphRootActualDegree")

MODULES.insert(MODULES.index("ShearSubstitution"), "OriginalMapFixedVertexDegree")

MODULES.insert(MODULES.index("ShearSubstitution"), "OriginalFixedVertexGeometricParabola")

MODULES.insert(MODULES.index("ShearSubstitution"), "OriginalGraphRootActualDegree")

MODULES.insert(MODULES.index("ShearSubstitution"), "OriginalGraphRootCoefficientData")

MODULES.insert(MODULES.index("ShearSubstitution"), "OriginalGraphRootForms")

MODULES.insert(MODULES.index("ShearSubstitution"), "GraphBoundaryFixedAxis")

MODULES.insert(MODULES.index("ShearSubstitution"), "ActualClosedGraphBoundaryRuling")

MODULES.insert(MODULES.index("ShearSubstitution"), "OriginalGraphRootVertex")

MODULES.insert(MODULES.index("ShearSubstitution"), "OriginalGraphCoefficientVertex")

MODULES.insert(MODULES.index("ShearSubstitution"), "OriginalGraphRootActualVertex")

MODULES.insert(MODULES.index("ShearSubstitution"), "OriginalFixedVertexDegreeAndBoundary")

MODULES.insert(MODULES.index("ShearSubstitution"), "CompatibleVertexParabola")

MODULES.insert(MODULES.index("ShearSubstitution"), "OriginalFixedVertexNonlinearExclusion")

MODULES.insert(MODULES.index("ShearSubstitution"), "ImageRelationConjugacy")

MODULES.insert(MODULES.index("ShearSubstitution"), "CommonVertexCoordinateChoice")

MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveRatioLinearCoordinates")

MODULES.insert(MODULES.index("ShearSubstitution"), "GaussDimensionConjugacy")

MODULES.insert(MODULES.index("ShearSubstitution"), "FullOutputLinearCoordinates")

MODULES.insert(MODULES.index("ShearSubstitution"), "SourceRealizationFiberComponent")

MODULES.insert(MODULES.index("ShearSubstitution"), "ConjugateOutputConstants")

MODULES.insert(MODULES.index("ShearSubstitution"), "GeometricComponentConjugacy")

MODULES.insert(MODULES.index("ShearSubstitution"), "CommonVertexNonlinearExclusion")

MODULES.insert(MODULES.index("ShearSubstitution"), "NonlinearGaussCharacteristic")

MODULES.insert(MODULES.index("ShearSubstitution"), "IndependentNormalPencilBase")

MODULES.insert(MODULES.index("ShearSubstitution"), "NonlinearNormalPencilBase")

MODULES.insert(MODULES.index("ShearSubstitution"), "IndependentNormalPlaneIncidence")

MODULES.insert(MODULES.index("ShearSubstitution"), "IndependentNormalScaledPowerExclusion")

MODULES.insert(MODULES.index("ShearSubstitution"), "IndependentNormalCharacteristicRoot")

MODULES.insert(MODULES.index("ShearSubstitution"), "OriginalNonlinearCharacteristicRoot")

MODULES.insert(MODULES.index("ShearSubstitution"), "CharacteristicRootMultiplicity")

MODULES.insert(MODULES.index("ShearSubstitution"), "CharacteristicRootSourceDivisorExclusion")

MODULES.insert(MODULES.index("ShearSubstitution"), "CharacteristicRootZeroDivisor")

MODULES.insert(MODULES.index("ShearSubstitution"), "CharacteristicPencilNoCommonDivisor")

MODULES.insert(MODULES.index("ShearSubstitution"), "CharacteristicPencilNonproportional")

MODULES.insert(MODULES.index("ShearSubstitution"), "CharacteristicGaussPencilGeometry")

MODULES.insert(MODULES.index("ShearSubstitution"), "OriginalNonlinearCharacteristicPencil")

MODULES.insert(MODULES.index("ShearSubstitution"), "FixedCurvePointFieldDimension")

MODULES.insert(MODULES.index("ShearSubstitution"), "CharacteristicRootFixedSourceCurve")

MODULES.insert(MODULES.index("ShearSubstitution"), "ValuationResidueLinearIndependence")

MODULES.insert(MODULES.index("ShearSubstitution"), "ValuationResidueSpanDimension")

MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectivePointHilbertEvaluation")

MODULES.insert(MODULES.index("ShearSubstitution"), "ValuationProjectiveHilbertSpecialization")

MODULES.insert(MODULES.index("ShearSubstitution"), "LocalPencilZero")

MODULES.insert(MODULES.index("ShearSubstitution"), "NativePencilStalkConstants")

MODULES.insert(MODULES.index("ShearSubstitution"), "CharacteristicPencilRegularZero")

MODULES.insert(MODULES.index("ShearSubstitution"), "CoefficientRestrictionValuation")

MODULES.insert(MODULES.index("ShearSubstitution"), "CoefficientRestrictionHilbertComparison")

MODULES.insert(MODULES.index("ShearSubstitution"), "NativeDivisorCoordinateHilbert")

MODULES.insert(MODULES.index("ShearSubstitution"), "CoefficientRestrictionCurveResidue")

MODULES.insert(MODULES.index("ShearSubstitution"), "PencilCoefficientCurveField")

MODULES.insert(MODULES.index("ShearSubstitution"), "RegularPencilCoefficientResidue")

MODULES.insert(MODULES.index("ShearSubstitution"), "CharacteristicPencilCoefficientResidue")

MODULES.insert(MODULES.index("ShearSubstitution"), "NativeProjectiveResidueIdeal")

MODULES.insert(MODULES.index("ShearSubstitution"), "CharacteristicPencilDivisorSpecialization")

MODULES.insert(MODULES.index("ShearSubstitution"), "OriginalNonlinearPencilSpecialization")

MODULES.insert(MODULES.index("ShearSubstitution"), "LinearPencilProjectiveField")

MODULES.insert(MODULES.index("ShearSubstitution"), "CharacteristicPencilOutputField")

MODULES.insert(MODULES.index("ShearSubstitution"), "NativeGraphRootIdentityTransfer")

MODULES.insert(MODULES.index("ShearSubstitution"), "IndependentRulingFiniteGraphBasis")

MODULES.insert(MODULES.index("ShearSubstitution"), "IndependentRulingGraphRootDegree")

MODULES.insert(MODULES.index("ShearSubstitution"), "OriginalFiberClosedCoefficientBoundary")

MODULES.insert(MODULES.index("ShearSubstitution"), "NativeIndependentOriginalFiberDegree")

MODULES.insert(MODULES.index("ShearSubstitution"), "CharacteristicRootOriginalFiberDegree")

MODULES.insert(MODULES.index("ShearSubstitution"), "OriginalNonlinearFiberDegreeTwo")

MODULES.insert(MODULES.index("ShearSubstitution"), "GeometricComponentDegreeComparison")

MODULES.insert(MODULES.index("ShearSubstitution"), "RationalScaleZeroLocalRing")

MODULES.insert(MODULES.index("ShearSubstitution"), "CoefficientRestrictionResidueRealization")

MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectivePointCoefficientComparison")

MODULES.insert(MODULES.index("ShearSubstitution"), "RationalScaleCoefficientResidue")

MODULES.insert(MODULES.index("ShearSubstitution"), "RationalScaleRelativeHilbert")

MODULES.insert(MODULES.index("ShearSubstitution"), "ScaledSourceRelativeCurveComparison")

MODULES.insert(MODULES.index("ShearSubstitution"), "RealizedOutputCoefficientAlgebraicity")

MODULES.insert(MODULES.index("ShearSubstitution"), "RootFactorizationScaledTarget")

MODULES.insert(MODULES.index("ShearSubstitution"), "CharacteristicScaleCoefficientImages")

MODULES.insert(MODULES.index("ShearSubstitution"), "OriginalFiberChartHilbertInvariance")

MODULES.insert(MODULES.index("ShearSubstitution"), "CharacteristicPencilOriginalHilbert")

MODULES.insert(MODULES.index("ShearSubstitution"), "CurveHilbertComparisonExistence")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectivePointTranscendenceLowerBound")

MODULES.insert(MODULES.index("ShearSubstitution"), "PencilCurveHilbertLowerBound")

MODULES.insert(MODULES.index("ShearSubstitution"), "OriginalRadialCurveDegreeExistence")

MODULES.insert(MODULES.index("ShearSubstitution"), "CharacteristicPencilDegreeTwo")

MODULES.insert(MODULES.index("ShearSubstitution"), "CharacteristicPencilDivisorDegreeTwo")
MODULES.insert(MODULES.index("ShearSubstitution"), "OriginalNonlinearPencilDegreeTwo")

MODULES.insert(MODULES.index("ShearSubstitution"), "CoefficientResidueCurveDegreeExistence")

MODULES.insert(MODULES.index("ShearSubstitution"), "NativeNormalizationChartGermAlgebra")

MODULES.insert(MODULES.index("ShearSubstitution"), "NativeDivisorResidueTranscendence")

MODULES.insert(MODULES.index("ShearSubstitution"), "NativePencilDivisorCurveDegreeExistence")

MODULES.insert(MODULES.index("ShearSubstitution"), "CharacteristicPencilSpecializedDegreeTwo")

MODULES.insert(MODULES.index("ShearSubstitution"), "NormalizationDivisorResidueParameter")

MODULES.insert(MODULES.index("ShearSubstitution"), "OriginalNonlinearPositiveSpecializationDegreeTwo")

MODULES.insert(MODULES.index("ShearSubstitution"), "PrimeLocalizationResidueField")

MODULES.insert(MODULES.index("ShearSubstitution"), "NativeTensorDivisorResidue")

MODULES.insert(MODULES.index("ShearSubstitution"), "NormalizationResidueValue")

MODULES.insert(MODULES.index("ShearSubstitution"), "DifferentialConstantLinearIndependence")

MODULES.insert(MODULES.index("ShearSubstitution"), "CurveDerivationCompatibility")

MODULES.insert(MODULES.index("ShearSubstitution"), "CurveCoefficientLinearDisjoint")

MODULES.insert(MODULES.index("ShearSubstitution"), "LinearlyDisjointProjectiveHilbert")

MODULES.insert(MODULES.index("ShearSubstitution"), "FixedCurveCoefficientDegreeDescent")

MODULES.insert(MODULES.index("ShearSubstitution"), "RestoredCoordinateField")

MODULES.insert(MODULES.index("ShearSubstitution"), "OriginalRootFixedCurveDegreeDescent")

MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveHilbertAlgebraTransport")
MODULES.insert(MODULES.index("ShearSubstitution"), "NativeDivisorFixedCurveDegreeTwo")
MODULES.insert(MODULES.index("ShearSubstitution"), "PolynomialDegreeIndependence")
MODULES.insert(MODULES.index("ShearSubstitution"), "PolynomialProductDimension")
MODULES.insert(MODULES.index("ShearSubstitution"), "PolynomialProjectiveHilbertGrowth")
MODULES.insert(MODULES.index("ShearSubstitution"), "CharacteristicImageDegreeLowerBound")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveHyperplaneIntersection")
MODULES.insert(MODULES.index("ShearSubstitution"), "NativeDivisorHyperplaneIntersection")
MODULES.insert(MODULES.index("ShearSubstitution"), "NativeRootSectionSpecialization")
MODULES.insert(MODULES.index("ShearSubstitution"), "CharacteristicRootPencilBasePoint")
MODULES.insert(MODULES.index("ShearSubstitution"), "SeparatedPencilGraphKernel")
MODULES.insert(MODULES.index("ShearSubstitution"), "CharacteristicRootStalkSeparation")
MODULES.insert(MODULES.index("ShearSubstitution"), "CharacteristicRootGenericGraph")
MODULES.insert(MODULES.index("ShearSubstitution"), "CharacteristicRootGenericBoundary")
MODULES.insert(MODULES.index("ShearSubstitution"), "RationalScalarBoundaryCoefficients")
MODULES.insert(MODULES.index("ShearSubstitution"), "GenericGraphScaledProjectiveBoundary")
MODULES.insert(MODULES.index("ShearSubstitution"), "CharacteristicRootScaledBoundary")
MODULES.insert(MODULES.index("ShearSubstitution"), "CharacteristicScaleParameterAlgebraicity")
MODULES.insert(MODULES.index("ShearSubstitution"), "NativeCharacteristicFullOutputEmbedding")
MODULES.insert(MODULES.index("ShearSubstitution"), "CompatibleExtensionBoundaryTransport")
MODULES.insert(MODULES.index("ShearSubstitution"), "CharacteristicRootOriginalBoundary")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectivePointCoefficientRestriction")
MODULES.insert(MODULES.index("ShearSubstitution"), "NativeSpecializationPointRelations")
MODULES.insert(MODULES.index("ShearSubstitution"), "AlgebraicProjectivePointLift")
MODULES.insert(MODULES.index("ShearSubstitution"), "RelativeSourceCoefficientRealization")
MODULES.insert(MODULES.index("ShearSubstitution"), "NativeRelativeGraphCoefficients")
MODULES.insert(MODULES.index("ShearSubstitution"), "NormalizedProjectivePointLift")
MODULES.insert(MODULES.index("ShearSubstitution"), "CharacteristicAlgebraicGraphBoundary")
MODULES.insert(MODULES.index("ShearSubstitution"), "NativeSpecifiedRootGraphTransfer")
MODULES.insert(MODULES.index("ShearSubstitution"), "NativeSpecifiedPowerBoundary")
MODULES.insert(MODULES.index("ShearSubstitution"), "ActualBoundaryChosenRuling")
MODULES.insert(MODULES.index("ShearSubstitution"), "RulingProportionalCovectorBaseChange")
MODULES.insert(MODULES.index("ShearSubstitution"), "CharacteristicNativePowerBoundary")
MODULES.insert(MODULES.index("ShearSubstitution"), "CharacteristicBoundaryDirection")
MODULES.insert(MODULES.index("ShearSubstitution"), "CompatibleAlgebraicGraphBoundaryLift")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveDirectionIdealContraction")
MODULES.insert(MODULES.index("ShearSubstitution"), "NativeCharacteristicIntersectionIdeal")
MODULES.insert(MODULES.index("ShearSubstitution"), "NativeCharacteristicRootContainment")

MODULES.insert(MODULES.index("ShearSubstitution"), "NativeDivisorSourceIdealTransport")

MODULES.insert(MODULES.index("ShearSubstitution"), "ChosenNonlinearCharacteristic")

MODULES.insert(MODULES.index("ShearSubstitution"), "ChosenCharacteristicOriginalIdeal")

MODULES.insert(MODULES.index("ShearSubstitution"), "NativeCharacteristicRootDegreeObstruction")

MODULES.insert(MODULES.index("ShearSubstitution"), "OriginalProportionalCharacteristicExclusion")

MODULES.insert(MODULES.index("ShearSubstitution"), "CharacteristicRootNonlinearExclusion")

MODULES.insert(MODULES.index("ShearSubstitution"), "DevelopableNonlinearExclusion")

MODULES.insert(MODULES.index("ShearSubstitution"), "SegreRulingRestrictionMatrix")

MODULES.insert(MODULES.index("ShearSubstitution"), "SegreRulingNilpotenceObstruction")

MODULES.insert(MODULES.index("ShearSubstitution"), "SegreRulingTangentReduction")

MODULES.insert(MODULES.index("ShearSubstitution"), "SegreRulingTangentFrame")

MODULES.insert(MODULES.index("ShearSubstitution"), "MatrixNilpotentIntertwiner")

MODULES.insert(MODULES.index("ShearSubstitution"), "SegreRulingHomogeneousProfiles")

MODULES.insert(MODULES.index("ShearSubstitution"), "SegreRulingLocalTangentModel")

MODULES.insert(MODULES.index("ShearSubstitution"), "SegreRulingLocalJacobianReduction")

MODULES.insert(MODULES.index("ShearSubstitution"), "SegreOriginalSourceChart")

MODULES.insert(MODULES.index("ShearSubstitution"), "SegreOriginalLocalOutputReduction")

MODULES.insert(MODULES.index("ShearSubstitution"), "SegreEulerDerivativeProfiles")

MODULES.insert(MODULES.index("ShearSubstitution"), "SegreEulerTangentObstruction")

MODULES.insert(MODULES.index("ShearSubstitution"), "SegreOriginalEulerWeights")

MODULES.insert(MODULES.index("ShearSubstitution"), "SegreOriginalResidueEuler")

MODULES.insert(MODULES.index("ShearSubstitution"), "SegrePrimitiveDegreeBound")

MODULES.insert(MODULES.index("ShearSubstitution"), "SegreOriginalResidueCoordinates")

MODULES.insert(MODULES.index("ShearSubstitution"), "SegreOriginalRulingLocalObstruction")

MODULES.insert(MODULES.index("ShearSubstitution"), "SegreRegularRulingRows")

MODULES.insert(MODULES.index("ShearSubstitution"), "SegreOriginalLocalPreservationExclusion")

MODULES.insert(MODULES.index("ShearSubstitution"), "UniformizerResidueDerivation")

MODULES.insert(MODULES.index("ShearSubstitution"), "SegreCanonicalResidueExclusion")

MODULES.insert(MODULES.index("ShearSubstitution"), "SegreOriginalSourceDivisor")

MODULES.insert(MODULES.index("ShearSubstitution"), "SegreOriginalDivisorCoordinates")

MODULES.insert(MODULES.index("ShearSubstitution"), "LocalizationDerivation")

MODULES.insert(MODULES.index("ShearSubstitution"), "LocalizationDerivationFieldCompatibility")

MODULES.insert(MODULES.index("ShearSubstitution"), "PrimeLocalizationPartials")

MODULES.insert(MODULES.index("ShearSubstitution"), "SegreOriginalDivisorDerivations")

MODULES.insert(MODULES.index("ShearSubstitution"), "SegreProjectiveRestrictionKernel")

MODULES.insert(MODULES.index("ShearSubstitution"), "SegreDominantNormalizedOutputs")

MODULES.insert(MODULES.index("ShearSubstitution"), "FiniteTrdegSelfEmbedding")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreRulingResiduePreservation")
MODULES.insert(MODULES.index("ShearSubstitution"), "ConeFieldDerivationGeneration")
MODULES.insert(MODULES.index("ShearSubstitution"), "DominantQuadricWronskian")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreResidueChartWeights")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreDominanceWronskian")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreOriginalFirstRulingExclusion")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveRestrictionKernelCriterion")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreRulingTranspose")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreOriginalRulingExclusion")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreGraphDifferentials")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreOriginalOutputChart")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreOriginalFiberInvariants")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreProjectiveBoundaryEquations")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreOriginalFiberWitness")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreFiberCoordinates")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreRulingBoundaryPoints")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreRealizedFiberNormalForm")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreOriginalGeometricNormalForm")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreProjectiveRulingPoints")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreOriginalTwoInfinityPoints")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreGenericRulingExclusion")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreActualBoundaryNonGeneric")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreRulingParameterField")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreRulingRelativeDimension")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreRulingMatrix")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreBoundaryRulingAlgebraicity")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreActualBoundaryAlgebraicity")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreRulingSourceKernel")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreBoundaryParameterField")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreFiniteBoundaryBranch")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreGeometricBoundaryNonGeneric")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreMappedRulingAlgebraicity")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreGeometricBoundaryAlgebraicity")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreFiniteProjectiveRulingPoint")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreGeometricRulingParameter")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreOriginalFiniteInfinityPoints")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveClosureRestrictCoefficients")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreRealizedBoundaryHessian")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreOriginalBoundaryHessian")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreRulingDirectionCalculus")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreRulingRootForms")
MODULES.insert(MODULES.index("ShearSubstitution"), "FullDimensionCoefficientEmbedding")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreAlgebraicBoundaryConstants")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreProjectiveRulingCoordinates")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreRealizedFiniteRootForms")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreFiniteRadialProductFactorization")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreOriginalRulingFactorizations")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreRulingBinaryPolynomial")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreNormalizedRulingPolynomial")
MODULES.insert(MODULES.index("ShearSubstitution"), "AlgebraicParameterReflection")
MODULES.insert(MODULES.index("ShearSubstitution"), "ClosedParameterPolynomialDescent")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreCommonFieldRulingPolynomials")
MODULES.insert(MODULES.index("ShearSubstitution"), "IteratedDerivationPolynomial")
MODULES.insert(MODULES.index("ShearSubstitution"), "AlgebraicParameterRepeatedIntegration")
MODULES.insert(MODULES.index("ShearSubstitution"), "PolynomialDifferentialCoefficients")
MODULES.insert(MODULES.index("ShearSubstitution"), "BivariateAlgebraicPolynomialDescent")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreRatioDerivations")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreCommonFieldBivariateDescent")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreCoefficientBivariateDescent")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreBivariateEvaluationTransport")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreOriginalBivariateSource")
MODULES.insert(MODULES.index("ShearSubstitution"), "BinaryLinearPowerHessian")
MODULES.insert(MODULES.index("ShearSubstitution"), "BinaryLinearPowerDescent")
MODULES.insert(MODULES.index("ShearSubstitution"), "FactorizationPowerRemainder")
MODULES.insert(MODULES.index("ShearSubstitution"), "NormalizedPrimeFactorProducts")
MODULES.insert(MODULES.index("ShearSubstitution"), "UnivariateLinearPowerDescent")
MODULES.insert(MODULES.index("ShearSubstitution"), "PowerRemainderUniqueness")
MODULES.insert(MODULES.index("ShearSubstitution"), "LinearPolynomialPowerRemainder")
MODULES.insert(MODULES.index("ShearSubstitution"), "FractionPolynomialPrimeLift")
MODULES.insert(MODULES.index("ShearSubstitution"), "PrimeExponentDivisibility")
MODULES.insert(MODULES.index("ShearSubstitution"), "FractionPolynomialPowerFree")
MODULES.insert(MODULES.index("ShearSubstitution"), "FractionPolynomialCanonicalFactors")
MODULES.insert(MODULES.index("ShearSubstitution"), "EquivPowerCanonicalFactors")
MODULES.insert(MODULES.index("ShearSubstitution"), "BivariateRulingPowerFactorization")
MODULES.insert(MODULES.index("ShearSubstitution"), "BivariateAlgebraicRulingFactors")
MODULES.insert(MODULES.index("ShearSubstitution"), "BivariateBilinearCoefficients")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreBilinearHyperplaneLift")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreRulingGlobalPowerReduction")
MODULES.insert(MODULES.index("ShearSubstitution"), "ClosedParameterVectorDescent")
MODULES.insert(MODULES.index("ShearSubstitution"), "RationalRulingPolynomialIdentity")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreCommonFieldRulingFactors")
MODULES.insert(MODULES.index("ShearSubstitution"), "TwoRationalRulingPresentations")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreCommonFactorsGlobalIdentity")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreCoefficientGlobalFactorization")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreGlobalFactorizationTransport")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreOriginalGlobalFactorization")
MODULES.insert(MODULES.index("ShearSubstitution"), "HomogeneousRationalPowerLinearForm")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreGlobalLinearRoot")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreOriginalLinearRoot")
MODULES.insert(MODULES.index("ShearSubstitution"), "LinearPowerRemainderRootUniqueness")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreQuadricHyperplaneRestriction")
MODULES.insert(MODULES.index("ShearSubstitution"), "RulingRemainderRootComparison")
MODULES.insert(MODULES.index("ShearSubstitution"), "FiniteParameterRemainderRoot")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreSelectedGlobalRemainder")
MODULES.insert(MODULES.index("ShearSubstitution"), "LinearPowerFiberInfinity")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreCoefficientSelectedRemainder")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreOriginalGlobalBoundaryIncidence")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreRulingHyperplaneDeterminant")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreTranscendentalRulingIncidence")
MODULES.insert(MODULES.index("ShearSubstitution"), "NilpotentProportionalLinearPower")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreNonzeroPairingExclusion")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreZeroPairingFiberEquations")
MODULES.insert(MODULES.index("ShearSubstitution"), "AffineFiberBoundaryLinearEquation")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreZeroPairingBoundary")
MODULES.insert(MODULES.index("ShearSubstitution"), "WeightedStationaryPowerSquare")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreZeroPairingSourceInvariants")
MODULES.insert(MODULES.index("ShearSubstitution"), "ParametricStationarySquare")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreRealizedZeroPairingBoundary")
MODULES.insert(MODULES.index("ShearSubstitution"), "ParametricStationarySquareForms")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreZeroPairingFiniteSquare")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreOriginalZeroPairingSquares")
MODULES.insert(MODULES.index("ShearSubstitution"), "SegreNormalizedSecondSquare")

MODULES.insert(MODULES.index("ShearSubstitution"), "SegreSecondSquareBivariateDescent")

MODULES.insert(MODULES.index("ShearSubstitution"), "UnivariateScalarLinearPowerDescent")

MODULES.insert(MODULES.index("ShearSubstitution"), "ScalarLinearPowerCanonicalFactors")

MODULES.insert(MODULES.index("ShearSubstitution"), "BivariateScalarLinearPowerFactorization")

MODULES.insert(MODULES.index("ShearSubstitution"), "SegreCommonFieldSecondSquares")

MODULES.insert(MODULES.index("ShearSubstitution"), "SegreSecondSquareGlobalIdentity")

MODULES.insert(MODULES.index("ShearSubstitution"), "SegreSecondSquareCoefficientIdentity")

MODULES.insert(MODULES.index("ShearSubstitution"), "SegreSecondSquareSourceTransport")

MODULES.insert(MODULES.index("ShearSubstitution"), "SegreOriginalSecondSquareIdentity")

MODULES.insert(MODULES.index("ShearSubstitution"), "SegreSplitLaplacian")

MODULES.insert(MODULES.index("ShearSubstitution"), "IrreduciblePolynomialSquareRoot")

MODULES.insert(MODULES.index("ShearSubstitution"), "SegreZeroPairingNormalRelation")

MODULES.insert(MODULES.index("ShearSubstitution"), "SegreNonlinearFiberExclusion")

MODULES.insert(MODULES.index("ShearSubstitution"), "QuadricCoordinateFiberExclusion")

MODULES.insert(MODULES.index("ShearSubstitution"), "NonlinearGeometricDependence")

MODULES.insert(MODULES.index("ShearSubstitution"), "InvariantVectorTraceConstraints")

MODULES.insert(MODULES.index("ShearSubstitution"), "TwoAxisKernelTraceReduction")

MODULES.insert(MODULES.index("ShearSubstitution"), "BinaryAnnihilatorEulerReduction")

MODULES.insert(MODULES.index("ShearSubstitution"), "NilpotentBinaryRadialPair")

MODULES.insert(MODULES.index("ShearSubstitution"), "BinaryBlockNilpotence")

MODULES.insert(MODULES.index("ShearSubstitution"), "PrimitiveBinaryDirection")

MODULES.insert(MODULES.index("ShearSubstitution"), "TwoAxisKernelRadialOutput")

MODULES.insert(MODULES.index("ShearSubstitution"), "NilpotentBinaryOutputPair")

MODULES.insert(MODULES.index("ShearSubstitution"), "ClassifiedBinaryDirectionDependence")
MODULES.insert(MODULES.index("ShearSubstitution"), "PolynomialKernelConjugacy")

MODULES.insert(MODULES.index("ShearSubstitution"), "PrimitivePolynomialConjugacy")

MODULES.insert(MODULES.index("ShearSubstitution"), "ClassifiedKernelCoordinateDependence")

MODULES.insert(MODULES.index("ShearSubstitution"), "PrimitiveVectorGenericAvoidance")

MODULES.insert(MODULES.index("ShearSubstitution"), "OriginalPrimitiveKernelNonvanishing")

MODULES.insert(MODULES.index("ShearSubstitution"), "NowhereZeroCollinearPolynomialVector")

MODULES.insert(MODULES.index("ShearSubstitution"), "GeometricComponentSourceEvaluation")
MODULES.insert(MODULES.index("ShearSubstitution"), "FullDimensionAffineLineParameter")

MODULES.insert(MODULES.index("ShearSubstitution"), "AffineLinePolynomialRestriction")

MODULES.insert(MODULES.index("ShearSubstitution"), "AffineLineKernelConstancy")

MODULES.insert(MODULES.index("ShearSubstitution"), "OriginalLineFiberKernelAcceleration")

MODULES.insert(MODULES.index("ShearSubstitution"), "ZeroAccelerationPolynomialTranslation")

MODULES.insert(MODULES.index("ShearSubstitution"), "OriginalRankThreeQuasiTranslationReduction")

MODULES.insert(MODULES.index("ShearSubstitution"), "PrimitiveHomogeneousQuasiTranslationRank")

MODULES.insert(MODULES.index("ShearSubstitution"), "PrimitiveTwoAxisQuasiTranslation")

MODULES.insert(MODULES.index("ShearSubstitution"), "IndependentCovectorPairCoordinates")

MODULES.insert(MODULES.index("ShearSubstitution"), "QuasiTranslationSpanReduction")

MODULES.insert(MODULES.index("ShearSubstitution"), "QuasiTranslationInvariantDivisors")

MODULES.insert(MODULES.index("ShearSubstitution"), "QuasiTranslationFiberDivisorTangency")

MODULES.insert(MODULES.index("ShearSubstitution"), "HomogeneousRankTwoProjectiveParameter")

MODULES.insert(MODULES.index("ShearSubstitution"), "HomogenizedParameterPencil")

MODULES.insert(MODULES.index("ShearSubstitution"), "SourcePencilProjectiveFibers")

MODULES.insert(MODULES.index("ShearSubstitution"), "PrimitiveQuasiTranslationSourcePencil")

MODULES.insert(MODULES.index("ShearSubstitution"), "GenericReducedHomogeneousPencil")

MODULES.insert(MODULES.index("ShearSubstitution"), "CofinitePolynomialParameterKernel")
MODULES.insert(MODULES.index("ShearSubstitution"), "HomogeneousPencilGradientIndependence")

MODULES.insert(MODULES.index("ShearSubstitution"), "QuasiTranslationPencilGradientKernel")

MODULES.insert(MODULES.index("ShearSubstitution"), "PrimitiveGordanNoetherSpan")

MODULES.insert(MODULES.index("ShearSubstitution"), "PrimitiveQuasiTranslationClassification")

MODULES.insert(MODULES.index("ShearSubstitution"), "ConstantKernelSourceReduction")

MODULES.insert(MODULES.index("ShearSubstitution"), "SmallerSourceDependenceTransport")

MODULES.insert(MODULES.index("ShearSubstitution"), "OriginalRankThreeTernaryReduction")

MODULES.insert(MODULES.index("ShearSubstitution"), "PrimitiveHomogenizedParameterVector")

MODULES.insert(MODULES.index("ShearSubstitution"), "PrimitiveVectorRationalScalar")

MODULES.insert(MODULES.index("ShearSubstitution"), "PolynomialSourcePencilFactorization")

MODULES.insert(MODULES.index("ShearSubstitution"), "HomogeneousRankTwoPolynomialPencil")

MODULES.insert(MODULES.index("ShearSubstitution"), "HomogeneousQuasiTranslationSpan")

MODULES.insert(MODULES.index("ShearSubstitution"), "QuasiTranslationDependenceDescent")

MODULES.insert(MODULES.index("ShearSubstitution"), "NilpotentThreeVectorOrbit")

MODULES.insert(MODULES.index("ShearSubstitution"), "IndependentVectorCoordinateColumns")

MODULES.insert(MODULES.index("ShearSubstitution"), "PolynomialJacobianPointEvaluation")

MODULES.insert(MODULES.index("ShearSubstitution"), "NilpotentJacobianNormalizedPointFrame")

MODULES.insert(MODULES.index("ShearSubstitution"), "BinaryPencilPointNormalization")

MODULES.insert(MODULES.index("ShearSubstitution"), "HomogenizedParameterSourceJets")

MODULES.insert(MODULES.index("ShearSubstitution"), "HomogeneousBinaryDehomogenization")

MODULES.insert(MODULES.index("ShearSubstitution"), "NormalizedJacobianParameterJets")

MODULES.insert(MODULES.index("ShearSubstitution"), "NormalizedRankTwoSourcePencil")

MODULES.insert(MODULES.index("ShearSubstitution"), "OriginalRankTwoNormalizedPencil")

MODULES.insert(MODULES.index("ShearSubstitution"), "NilpotentPencilMinorDivisibility")

MODULES.insert(MODULES.index("ShearSubstitution"), "NormalizedPencilActiveMinor")

MODULES.insert(MODULES.index("ShearSubstitution"), "SimplePointPrimePencilFactor")

MODULES.insert(MODULES.index("ShearSubstitution"), "OriginalRankTwoPrimePencilFactor")

MODULES.insert(MODULES.index("ShearSubstitution"), "FullDimensionDerivationConstants")
MODULES.insert(MODULES.index("ShearSubstitution"), "PrincipalQuotientDerivation")

MODULES.insert(MODULES.index("ShearSubstitution"), "PrimeSourcePlaneDerivation")

MODULES.insert(MODULES.index("ShearSubstitution"), "PrimePencilProjectionRelation")

MODULES.insert(MODULES.index("ShearSubstitution"), "FixedPlaneProjectionPolynomial")

MODULES.insert(MODULES.index("ShearSubstitution"), "HomogeneousPencilProjectionEquation")

MODULES.insert(MODULES.index("ShearSubstitution"), "HomogeneousFixedPlanePrimeLinearRelation")

MODULES.insert(MODULES.index("ShearSubstitution"), "PencilProjectionLinearBaseComponent")

MODULES.insert(MODULES.index("ShearSubstitution"), "OriginalRankTwoLinearBaseComponent")

MODULES.insert(MODULES.index("ShearSubstitution"), "PolynomialWronskianIndependence")

MODULES.insert(MODULES.index("ShearSubstitution"), "ParametricDerivationMinor")

MODULES.insert(MODULES.index("ShearSubstitution"), "ParametricCovectorOrbitMinor")

MODULES.insert(MODULES.index("ShearSubstitution"), "NormalizedPencilOrbitMinor")

MODULES.insert(MODULES.index("ShearSubstitution"), "OriginalRankTwoOrbitMinors")

MODULES.insert(MODULES.index("ShearSubstitution"), "FiniteCovectorOrbitFrame")

MODULES.insert(MODULES.index("ShearSubstitution"), "CovectorPlaneFrameExclusion")

MODULES.insert(MODULES.index("ShearSubstitution"), "OriginalRankTwoFinitePlaneAvoidance")

MODULES.insert(MODULES.index("ShearSubstitution"), "PrimeConstantCovectorDimension")

MODULES.insert(MODULES.index("ShearSubstitution"), "TwoDimensionalCovectorCover")

MODULES.insert(MODULES.index("ShearSubstitution"), "RankTwoPencilBaseFrameAvoidance")

MODULES.insert(MODULES.index("ShearSubstitution"), "PrimitiveVectorFactorUniqueness")

MODULES.insert(MODULES.index("ShearSubstitution"), "IntrinsicPrimitivePencilBase")

MODULES.insert(MODULES.index("ShearSubstitution"), "PrescribedNormalizedPencilProjection")

MODULES.insert(MODULES.index("ShearSubstitution"), "PrimitiveBaseConjugacy")

MODULES.insert(MODULES.index("ShearSubstitution"), "InverseFrameFixedPlaneCovector")

MODULES.insert(MODULES.index("ShearSubstitution"), "IntrinsicPencilFrameContradiction")

MODULES.insert(MODULES.index("ShearSubstitution"), "HomogeneousRankTwoNilpotentDependence")

MODULES.insert(MODULES.index("ShearSubstitution"), "OriginalFieldRankTwoNilpotentDependence")

MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryQuasiTranslationDependence")

MODULES.insert(MODULES.index("ShearSubstitution"), "GeneralHomogeneousProjectiveField")
MODULES.insert(MODULES.index("ShearSubstitution"), "GeneralRationalSourceCurveField")

MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryNormalizedPointFrame")

MODULES.insert(MODULES.index("ShearSubstitution"), "GeneralHomogeneousRankTwoPencil")

MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryNormalizedParameterJets")

MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryNilpotentPencilMinor")

MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryNormalizedPencil")

MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryPrimeProjectionRelation")
MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryFixedAxisProjectionPolynomial")

MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryHomogeneousPencilBaseEquation")

MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryFixedAxisPrime")

MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryPrimeCovectorDimension")
MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryCovectorPlaneCover")

MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryPencilOrbitMinor")
MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryFiniteOrbitFrame")
MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryCovectorFrameExclusion")

MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryPrescribedPencilProjection")

MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryPencilBaseFrameAvoidance")

MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryIntrinsicFrameContradiction")

MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryHomogeneousNilpotentDependence")

MODULES.insert(MODULES.index("ShearSubstitution"), "OriginalFieldTernaryDependence")
MODULES.insert(MODULES.index("ShearSubstitution"), "HomogeneousDependenceTheorem")

MODULES.insert(MODULES.index("ShearSubstitution"), "FixedCoordinateReduction")

MODULES.insert(MODULES.index("ShearSubstitution"), "LastCoordinateDehomogenization")

MODULES.insert(MODULES.index("ShearSubstitution"), "NormalizedFixedCoordinateReduction")

MODULES.insert(MODULES.index("ShearSubstitution"), "FixedCoordinateTranslation")

MODULES.insert(MODULES.index("ShearSubstitution"), "LinearTameConjugacy")

MODULES.insert(MODULES.index("ShearSubstitution"), "FixedCoordinateTamenessReduction")

MODULES.insert(MODULES.index("ShearSubstitution"), "TamenessTheoremSpecification")

MODULES.insert(MODULES.index("ShearSubstitution"), "VandermondeSubmodulePolarization")

MODULES.insert(MODULES.index("ShearSubstitution"), "QuadraticInvariantFlow")

MODULES.insert(MODULES.index("ShearSubstitution"), "QuadraticFlowElementaryParameters")

MODULES.insert(MODULES.index("ShearSubstitution"), "QuadraticFlowParameterConjugacy")

MODULES.insert(MODULES.index("ShearSubstitution"), "QuadraticFlowTameness")

MODULES.insert(MODULES.index("ShearSubstitution"), "DeterminantShearFamily")

MODULES.insert(MODULES.index("ShearSubstitution"), "SplitQuadraticShearFlows")

MODULES.insert(MODULES.index("ShearSubstitution"), "DeterminantShearCoefficientConjugacy")

MODULES.insert(MODULES.index("ShearSubstitution"), "DeterminantShearCoefficientPolarization")

MODULES.insert(MODULES.index("ShearSubstitution"), "SplitDeterminantShearFactorization")

MODULES.insert(MODULES.index("ShearSubstitution"), "DeterminantShearAlphaOnly")

MODULES.insert(MODULES.index("ShearSubstitution"), "ConstructiveDeterminantShearTameness")

MODULES.insert(MODULES.index("ShearSubstitution"), "DeterminantShearCoefficientIdentity")

MODULES.insert(MODULES.index("ShearSubstitution"), "ConstantCoefficientShearTameness")

MODULES.insert(MODULES.index("ShearSubstitution"), "CoprimeLinearShearCoordinates")

MODULES.insert(MODULES.index("ShearSubstitution"), "LinearBaseShearFrame")

MODULES.insert(MODULES.index("ShearSubstitution"), "LinearCoefficientShearTameness")

MODULES.insert(MODULES.index("ShearSubstitution"), "Proposition64LowDegree")

MODULES.insert(MODULES.index("ShearSubstitution"), "HomogenizedTernaryNormalForm")

MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryNormalFormFirstFactor")

MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryNormalFormElementaryFactors")

MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryNormalFormCommutatorIdentity")

MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryNormalFormTameWord")

MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryNormalFormAffineChart")

MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryNormalFormJacobian")

MODULES.insert(MODULES.index("ShearSubstitution"), "HomogeneousMatrixBlockNilpotence")

MODULES.insert(MODULES.index("ShearSubstitution"), "Proposition66")

MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryNormalFormDegreeBound")

MODULES.insert(MODULES.index("ShearSubstitution"), "FixedCoordinateChartLinearConjugacy")

MODULES.insert(MODULES.index("ShearSubstitution"), "OriginalMapTamenessFromTernaryNormalForm")

MODULES.insert(MODULES.index("ShearSubstitution"), "PlanarShearCoefficientRing")

MODULES.insert(MODULES.index("ShearSubstitution"), "AffineLineLeadingComponent")

MODULES.insert(MODULES.index("ShearSubstitution"), "DerivationInvariantPlanarLine")

MODULES.insert(MODULES.index("ShearSubstitution"), "PlanarBinarySlopeAlgebraicity")

MODULES.insert(MODULES.index("ShearSubstitution"), "PlanarNilpotentSlopeIdentity")

MODULES.insert(MODULES.index("ShearSubstitution"), "PlanarNilpotentDependence")

MODULES.insert(MODULES.index("ShearSubstitution"), "PlanarActiveNormalization")

MODULES.insert(MODULES.index("ShearSubstitution"), "PlanarActiveFractionFieldDependence")

MODULES.insert(MODULES.index("ShearSubstitution"), "PlanarGroupedHomogeneousCoefficients")

MODULES.insert(MODULES.index("ShearSubstitution"), "PlanarCoefficientRelationDescent")

MODULES.insert(MODULES.index("ShearSubstitution"), "PlanarPrimitiveShearFactor")

MODULES.insert(MODULES.index("ShearSubstitution"), "PlanarInvariantPolynomialKernel")

MODULES.insert(MODULES.index("ShearSubstitution"), "CoprimeFractionCoefficientDescent")

MODULES.insert(MODULES.index("ShearSubstitution"), "PlanarShearInvariantFractionPolynomial")

MODULES.insert(MODULES.index("ShearSubstitution"), "PlanarInvariantCoefficientDescent")

MODULES.insert(MODULES.index("ShearSubstitution"), "PlanarInvariantAxisCoefficients")

MODULES.insert(MODULES.index("ShearSubstitution"), "PlanarShearPolynomialRepresentation")

MODULES.insert(MODULES.index("ShearSubstitution"), "PlanarShearParameterDegrees")

MODULES.insert(MODULES.index("ShearSubstitution"), "PlanarNonzeroShearNormalForm")

MODULES.insert(MODULES.index("ShearSubstitution"), "PlanarElementaryNormalForm")

MODULES.insert(MODULES.index("ShearSubstitution"), "PlanarTargetTranslation")

MODULES.insert(MODULES.index("ShearSubstitution"), "Proposition63")

MODULES.insert(MODULES.index("ShearSubstitution"), "QuinticPlanarParameter")

MODULES.insert(MODULES.index("ShearSubstitution"), "PolynomialAutomorphismStabilization")

MODULES.insert(MODULES.index("ShearSubstitution"), "StabilizationPreservesTameness")

MODULES.insert(MODULES.index("ShearSubstitution"), "StableTamenessComposition")

MODULES.insert(MODULES.index("ShearSubstitution"), "PlanarTamenessReduction")

MODULES.insert(MODULES.index("ShearSubstitution"), "DependentTernaryChartPlanarConjugacy")

MODULES.insert(MODULES.index("ShearSubstitution"), "PlanarBlockNilpotence")

MODULES.insert(MODULES.index("ShearSubstitution"), "StableTameConjugacy")

MODULES.insert(MODULES.index("ShearSubstitution"), "StableFixedCoordinateTameness")

MODULES.insert(MODULES.index("ShearSubstitution"), "FixedCoordinateChartNilpotence")

MODULES.insert(MODULES.index("ShearSubstitution"), "DependentTernaryChartTameness")

MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryClassificationSpecification")

MODULES.insert(MODULES.index("ShearSubstitution"), "ConditionalTamenessTheorem")

MODULES.insert(MODULES.index("ShearSubstitution"), "BinaryPencilDeterminantIdentity")

MODULES.insert(MODULES.index("ShearSubstitution"), "SimpleRootSplitsBinaryQuadratic")

MODULES.insert(MODULES.index("ShearSubstitution"), "BinaryPencilSimpleSpecialization")

MODULES.insert(MODULES.index("ShearSubstitution"), "HomogeneousBinaryQuadraticCoefficients")

MODULES.insert(MODULES.index("ShearSubstitution"), "CoprimeBinaryPencilLeadingMinors")

MODULES.insert(MODULES.index("ShearSubstitution"), "CoprimeBinaryPencilSplitMember")

MODULES.insert(MODULES.index("ShearSubstitution"), "SplitBinaryPencilBaseChange")

MODULES.insert(MODULES.index("ShearSubstitution"), "BinaryPencilBasisCoprimality")

MODULES.insert(MODULES.index("ShearSubstitution"), "NormalizeBinaryPencilSecondForm")

MODULES.insert(MODULES.index("ShearSubstitution"), "NormalizeBinaryQuadraticPencil")

MODULES.insert(MODULES.index("ShearSubstitution"), "QuinticPolynomialCoordinates")

MODULES.insert(MODULES.index("ShearSubstitution"), "QuinticAuxiliaryFlowIdentities")

MODULES.insert(MODULES.index("ShearSubstitution"), "QuinticInvariantFlowSign")

MODULES.insert(MODULES.index("ShearSubstitution"), "ActivePencilLinearFrame")

MODULES.insert(MODULES.index("ShearSubstitution"), "QuinticAuxiliaryGrouping")

MODULES.insert(MODULES.index("ShearSubstitution"), "QuinticCommutatorCoordinates")

MODULES.insert(MODULES.index("ShearSubstitution"), "QuinticDeterminantShearCoordinates")

MODULES.insert(MODULES.index("ShearSubstitution"), "QuinticAffineShearFrames")

MODULES.insert(MODULES.index("ShearSubstitution"), "ActivePencilPerturbationConjugacy")

MODULES.insert(MODULES.index("ShearSubstitution"), "BinaryPencilScalarShearIdentity")

MODULES.insert(MODULES.index("ShearSubstitution"), "BinaryPencilActiveConjugacy")

MODULES.insert(MODULES.index("ShearSubstitution"), "QuinticSecondLiftFlow")

MODULES.insert(MODULES.index("ShearSubstitution"), "QuinticPlaneShears")

MODULES.insert(MODULES.index("ShearSubstitution"), "QuinticParameterShifting")

MODULES.insert(MODULES.index("ShearSubstitution"), "QuinticCoefficientPlaneTranslations")

MODULES.insert(MODULES.index("ShearSubstitution"), "BinaryPencilBaseFrame")

MODULES.insert(MODULES.index("ShearSubstitution"), "BinaryPencilBaseTameness")

MODULES.insert(MODULES.index("ShearSubstitution"), "QuadraticPencilShearTransport")

MODULES.insert(MODULES.index("ShearSubstitution"), "QuinticSecondLiftTameShears")

MODULES.insert(MODULES.index("ShearSubstitution"), "QuinticSecondFlowTameness")

MODULES.insert(MODULES.index("ShearSubstitution"), "QuinticStateSubstitution")

MODULES.insert(MODULES.index("ShearSubstitution"), "QuinticSecondFlowTameWord")

MODULES.insert(MODULES.index("ShearSubstitution"), "QuinticSecondLiftAuxiliaryCoordinates")

MODULES.insert(MODULES.index("ShearSubstitution"), "QuinticFirstLiftAuxiliaryCoordinates")

MODULES.insert(MODULES.index("ShearSubstitution"), "QuinticGroupedAuxiliaryFactors")

MODULES.insert(MODULES.index("ShearSubstitution"), "QuinticTriangularFrameShear")

MODULES.insert(MODULES.index("ShearSubstitution"), "QuinticGroupedFirstTameness")

MODULES.insert(MODULES.index("ShearSubstitution"), "QuinticGroupedSecondTameness")

MODULES.insert(MODULES.index("ShearSubstitution"), "QuinticBasicLiftCoordinates")

MODULES.insert(MODULES.index("ShearSubstitution"), "QuinticBasicLiftTameness")

MODULES.insert(MODULES.index("ShearSubstitution"), "QuinticAuxiliaryOnlyFlowTameness")

MODULES.insert(MODULES.index("ShearSubstitution"), "QuinticGroupedTameWord")

MODULES.insert(MODULES.index("ShearSubstitution"), "QuinticAuxiliaryLiftFaithfulness")

MODULES.insert(MODULES.index("ShearSubstitution"), "QuinticInverseFlowLift")

MODULES.insert(MODULES.index("ShearSubstitution"), "QuinticInvolution")

MODULES.insert(MODULES.index("ShearSubstitution"), "QuinticCommutatorAuxiliaryLift")

MODULES.insert(MODULES.index("ShearSubstitution"), "NormalizedQuinticShearCoordinates")

MODULES.insert(MODULES.index("ShearSubstitution"), "Proposition67")

MODULES.insert(MODULES.index("ShearSubstitution"), "Corollary610")

MODULES.insert(MODULES.index("ShearSubstitution"), "Proposition611")

MODULES.insert(MODULES.index("ShearSubstitution"), "TamenessFromTernaryClassification")

MODULES.insert(MODULES.index("ShearSubstitution"), "QuinticPrintedFlowCoordinates")

MODULES.insert(MODULES.index("ShearSubstitution"), "QuinticOriginalFlowFormula")

MODULES.insert(MODULES.index("ShearSubstitution"), "TopPolynomialMatrixCoefficients")

MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryHighestHomogeneousPart")

MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryPlanarSpecialization")

MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryPlanarConstantRelation")

MODULES.insert(MODULES.index("ShearSubstitution"), "LinearConjugacyComposition")

MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryFixedCoordinateTriangularForm")

MODULES.insert(MODULES.index("ShearSubstitution"), "HomogeneousTernaryTriangularFrame")

MODULES.insert(MODULES.index("ShearSubstitution"), "BinaryHomogeneousConstantRootCover")

MODULES.insert(MODULES.index("ShearSubstitution"), "LinearConjugacyEvaluationExtension")

MODULES.insert(MODULES.index("ShearSubstitution"), "TriangularTernaryBasepointCover")

MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryHighestPartConstantPlanes")

MODULES.insert(MODULES.index("ShearSubstitution"), "RankSelectionOfIndependentOutputs")

MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryGraphCrossIdentities")

MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryJacobianDerivation")

MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryGraphPlaneInvariant")

MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryGraphPlaneDifferentiation")

MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryGraphQuadraticInvariant")

MODULES.insert(MODULES.index("ShearSubstitution"), "ClosedFieldCoefficientPartials")

MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryGraphNonzeroHessian")

MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryGraphCoordinateField")

MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryGraphQuadraticEquation")

MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryGraphRelationIdeal")

MODULES.insert(MODULES.index("ShearSubstitution"), "AffineSubstitutionLeadingValue")

MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryGraphInfinityValues")

MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryGraphCurve")

MODULES.insert(MODULES.index("ShearSubstitution"), "PolynomialParameterTraceSpecialization")

MODULES.insert(MODULES.index("ShearSubstitution"), "RankOnePolynomialParameterDependence")

MODULES.insert(MODULES.index("ShearSubstitution"), "ClosedRationalSourceCurveField")

MODULES.insert(MODULES.index("ShearSubstitution"), "NormalSourcePolynomialParameter")

MODULES.insert(MODULES.index("ShearSubstitution"), "PolynomialSourceRationalFieldIntersection")

MODULES.insert(MODULES.index("ShearSubstitution"), "ClosedPolynomialCurveParameter")

MODULES.insert(MODULES.index("ShearSubstitution"), "NormalizedTernaryJacobianRank")

MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryIndependentOutputChart")

MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryConstantRightKernelDependence")

MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryLineSlopeTrace")

MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryLineSlopeAlgebraicity")

MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryGraphLineDirection")

MODULES.insert(MODULES.index("ShearSubstitution"), "SpecifiedCovectorPairFrame")

MODULES.insert(MODULES.index("ShearSubstitution"), "LinearConjugacyDerivationTransport")

MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryLineConstantPlaneExclusion")

MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryGraphConic")

MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryChartCoefficientTransport")

MODULES.insert(MODULES.index("ShearSubstitution"), "BinaryQuadraticInfinityDirections")

MODULES.insert(MODULES.index("ShearSubstitution"), "QuadraticFiberLeadingBinaryValue")

MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryGraphCovectorRestriction")

MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryGraphPairIndependence")

MODULES.insert(MODULES.index("ShearSubstitution"), "ConstantCovectorDirectionSeparation")

MODULES.insert(MODULES.index("ShearSubstitution"), "AffineLeadingComponentPolynomialIdentity")

MODULES.insert(MODULES.index("ShearSubstitution"), "TransportedAffineCurveRelation")

MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryGraphAffineChartChange")

MODULES.insert(MODULES.index("ShearSubstitution"), "BinaryOutputPartialConstants")

MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryGraphRankOneHessian")

MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryGraphMixedHessian")

MODULES.insert(MODULES.index("ShearSubstitution"), "QuadraticHessianLinearTransport")

MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryConicChartTransport")

MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryConicWitness")

MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryConicHessianAssociation")

MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryConicFrames")

MODULES.insert(MODULES.index("ShearSubstitution"), "QuadricAxisEvaluation")

MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryConicSingularDirection")

MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryConicDistinctDirections")

MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryPolynomialLastVariable")

MODULES.insert(MODULES.index("ShearSubstitution"), "BilinearLeadingCoefficientObstruction")

MODULES.insert(MODULES.index("ShearSubstitution"), "BilinearLastDegreeObstructions")

MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryBilinearTraceMinor")

MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryBilinearOneMovingOutput")

MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryBilinearOutputExclusion")

MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryAlgebraicPairFrame")

MODULES.insert(MODULES.index("ShearSubstitution"), "ClosedFieldTernaryAlgebraicPair")
MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryClosedPolynomialParameter")
MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryParameterTraceMinors")
MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryParameterSlopeFrame")
MODULES.insert(MODULES.index("ShearSubstitution"), "FullBasisPartials")
MODULES.insert(MODULES.index("ShearSubstitution"), "DerivationSlicePolynomial")
MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryParameterCubicObstruction")
MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryParameterTransverseConstants")
MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryParameterRationalOutput")
MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryParameterPolynomialCoefficients")
MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryParameterPolynomialOutput")
MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryParameterQuadraticPotential")
MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryQuadraticGraphOutput")
MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryVerticalParameterChart")
MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryQuadraticGraphIdentity")
MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryBinaryQuadraticRank")
MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryRankOneGraphNormalForm")
MODULES.insert(MODULES.index("ShearSubstitution"), "ClosedFieldTernaryNormalForm")
MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryNormalFormRelation")
MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryQuadraticRelationTransport")
MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryNormalizationCovectorDescent")
MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryOriginalCoefficientMaps")
MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryOuterFrameDescent")
MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryOuterNormalizerFormula")
MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryOriginalParabolicNormalForm")
MODULES.insert(MODULES.index("ShearSubstitution"), "TernaryParabolicCoefficientDescent")
MODULES.insert(MODULES.index("ShearSubstitution"), "OriginalFieldTernaryClassification")
MODULES.insert(MODULES.index("ShearSubstitution"), "Proposition23")
MODULES.insert(MODULES.index("ShearSubstitution"), "FixedLastFiberEquations")
MODULES.insert(MODULES.index("ShearSubstitution"), "GenericFiberOutputEquations")
MODULES.insert(MODULES.index("ShearSubstitution"), "AffinePlaneCurveElimination")
MODULES.insert(MODULES.index("ShearSubstitution"), "ScalarActionOnFiberPrimes")
MODULES.insert(MODULES.index("ShearSubstitution"), "HomogeneousGenericFiberAction")
MODULES.insert(MODULES.index("ShearSubstitution"), "FixedLastGeometricFiberValue")
MODULES.insert(MODULES.index("ShearSubstitution"), "Corollary53ScalarAction")
MODULES.insert(MODULES.index("ShearSubstitution"), "FixedLastGeometricPlaneChart")
MODULES.insert(MODULES.index("ShearSubstitution"), "AffinePlaneCurveDichotomy")
MODULES.insert(MODULES.index("ShearSubstitution"), "PositiveCharacteristicExample")
MODULES.insert(MODULES.index("ShearSubstitution"), "Corollary53")
MODULES.insert(MODULES.index("ShearSubstitution"), "AffinePlaneConicCoordinates")
MODULES.insert(MODULES.index("ShearSubstitution"), "ConjugateGeometricFiberPoint")
MODULES.insert(MODULES.index("ShearSubstitution"), "Corollary53OriginalCoordinates")
MODULES.insert(MODULES.index("ShearSubstitution"), "PlaneConicExample")
MODULES.insert(MODULES.index("ShearSubstitution"), "PlaneConicExampleFiber")
MODULES.insert(MODULES.index("ShearSubstitution"), "ActualGaussDevelopableClassification")
MODULES.insert(MODULES.index("ShearSubstitution"), "HypersurfaceLineSpace")
MODULES.insert(MODULES.index("ShearSubstitution"), "PencilDivisorCurveDegree")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProperBirationalDivisorLift")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectivePencilFiberDegree")
MODULES.insert(MODULES.index("ShearSubstitution"), "OriginalPencilDivisorBound")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveBoundaryImageClosure")
MODULES.insert(MODULES.index("ShearSubstitution"), "ActualGaussClosedBoundaryImage")
MODULES.insert(MODULES.index("ShearSubstitution"), "SchemeModuleCategoricalFrames")
MODULES.insert(MODULES.index("ShearSubstitution"), "SchemeSectionVanishingDivisor")
MODULES.insert(MODULES.index("ShearSubstitution"), "Lemma44")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveHyperplaneCategoricalFrames")
MODULES.insert(MODULES.index("ShearSubstitution"), "NativeHyperplaneNormRegularity")
MODULES.insert(MODULES.index("ShearSubstitution"), "SheafModuleLocalMorphisms")
MODULES.insert(MODULES.index("ShearSubstitution"), "SchemeLineFrameAtlas")
MODULES.insert(MODULES.index("ShearSubstitution"), "SchemeLineFramePullback")
MODULES.insert(MODULES.index("ShearSubstitution"), "CategoricalProjectiveHyperplanePullback")
MODULES.insert(MODULES.index("ShearSubstitution"), "ProjectiveHyperplaneAmpleness")
MODULES.insert(MODULES.index("ShearSubstitution"), "NormalizedPencilHyperplaneDegree")
MODULES.insert(MODULES.index("ShearSubstitution"), "NormalizedPencilCategoricalMultiplicity")
MODULES.insert(MODULES.index("ShearSubstitution"), "NormalizedPencilHyperplaneAmpleness")

# Derive the build order from actual local imports, including support
# modules added after an earlier theorem has been strengthened.
ordered_modules, ordered_set, visiting_modules = [], set(), set()
def order_local_module(name):
    if name in ordered_set:
        return
    assert name not in visiting_modules, f"Local import cycle at {name}"
    visiting_modules.add(name)
    source = ROOT / ("DimensionFourDependence.lean" if name == "Main" else f"DimensionFourDependence/{name}.lean")
    for dependency in re.findall(r"^import DimensionFourDependence\.([A-Za-z0-9_]+)\s*$", source.read_text(encoding="utf-8"), re.M):
        assert dependency in MODULES, f"Missing compilation target {dependency}"
        order_local_module(dependency)
    visiting_modules.remove(name)
    ordered_set.add(name)
    ordered_modules.append(name)
for module_name in MODULES:
    order_local_module(module_name)
MODULES = ordered_modules
assert len(MODULES) == len(set(MODULES)), "Duplicate compilation target in MODULES"
assert set(MODULES) == {p.stem for p in (ROOT / "DimensionFourDependence").glob("*.lean")} | {"Main"}, "MODULES does not match the proof sources"
parser = argparse.ArgumentParser()
parser.add_argument("--module", choices=MODULES)
parser.add_argument("--timeout", type=int, default=1200)
parser.add_argument("--profile", action="store_true")
parser.add_argument("--lean-bin", type=Path, default=Path.home() / ".cache/lean4/lean-4.34.0-windows/bin")
parser.add_argument("--packages", type=Path, default=ROOT.parent / "quartic_dependence/.lake/packages")
args = parser.parse_args()
sys.stdout.reconfigure(encoding="utf-8")
build = ROOT / ".lake/build/lib/lean"
(build / "DimensionFourDependence").mkdir(parents=True, exist_ok=True)
(ROOT / "validation").mkdir(exist_ok=True)
env = os.environ.copy()
env["LEAN_PATH"] = os.pathsep.join(map(str, [build, ROOT] + [p / ".lake/build/lib/lean" for p in args.packages.iterdir() if p.is_dir()]))
results = []
for name in ([args.module] if args.module else MODULES):
    source = ROOT / ("DimensionFourDependence.lean" if name == "Main" else "DimensionFourDependence/" + name + ".lean")
    output = build / ("DimensionFourDependence.olean" if name == "Main" else "DimensionFourDependence/" + name + ".olean")
    start = time.monotonic()
    try:
        command = [str(args.lean_bin / "lean.exe")] + (["--profile"] if args.profile else []) + ["-o", str(output), str(source)]
        result = subprocess.run(command, cwd=ROOT, env=env, capture_output=True, encoding="utf-8", timeout=args.timeout)
        code, log = result.returncode, result.stdout + result.stderr
    except subprocess.TimeoutExpired as error:
        def decode(value):
            return value.decode("utf-8", errors="replace") if isinstance(value, bytes) else value or ""
        code = 124
        log = decode(error.stdout) + decode(error.stderr) + f"\nCompilation exceeded {args.timeout}s.\n"
    record = dict(file=source.relative_to(ROOT).as_posix(), source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(), exit_code=code, seconds=round(time.monotonic()-start, 2), log=log)
    results.append(record)
    (ROOT / "validation" / (name + ".json")).write_text(json.dumps(record, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"{name}: exit {code} ({record['seconds']}s)", flush=True)
    print(record["log"], end="", flush=True)
    if code:
        sys.exit(code)
if not args.module:
    (ROOT / "validation/results.json").write_text(json.dumps(results, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
