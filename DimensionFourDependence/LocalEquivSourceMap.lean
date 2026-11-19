import DimensionFourDependence.LocalEquivOrderTransport

/-! # The original source-local map through a normalization isomorphism

The inverse local isomorphism constructs a source-local algebra map
that preserves the original source ring. Its values upstairs are the
original source-local values, rather than unrelated local coordinates.
-/

namespace DimensionFourDependence

variable {R O A B : Type*} [CommRing R] [CommRing O] [CommRing A] [CommRing B]
  [Algebra R O] [Algebra R A] [Algebra R B] [Algebra O B] [IsScalarTower R O B]

/-- The original source-local ring in the actual normalization local ring. -/
noncomputable def localEquivSourceAlgHom (e : A ≃ₐ[R] B) : O →ₐ[R] A :=
  e.symm.toAlgHom.comp (IsScalarTower.toAlgHom R O B)

/-- Every descended local source value has its original upstairs value. -/
theorem localEquivSourceAlgHom_target (e : A ≃ₐ[R] B) (x : O) :
    e (localEquivSourceAlgHom (O := O) e x) = algebraMap O B x :=
  e.apply_symm_apply _

/-- The descended source-local map retains every original source function. -/
theorem localEquivSourceAlgHom_original_source (e : A ≃ₐ[R] B) (r : R) :
    localEquivSourceAlgHom (O := O) e (algebraMap R O r) = algebraMap R A r :=
  (localEquivSourceAlgHom (O := O) e).commutes r

/-- The constructed action of the original source-local ring. -/
@[instance_reducible]
noncomputable def localEquivSourceAlgebra (e : A ≃ₐ[R] B) : Algebra O A :=
  (localEquivSourceAlgHom (O := O) e).toRingHom.toAlgebra

/-- With that constructed action the normalization local isomorphism
is an isomorphism over the original source-local ring itself. -/
noncomputable def localEquivOverSource (e : A ≃ₐ[R] B) :
    letI : Algebra O A := localEquivSourceAlgebra (O := O) e
    A ≃ₐ[O] B := by
  let : Algebra O A := localEquivSourceAlgebra (O := O) e
  exact { e.toRingEquiv with commutes' := localEquivSourceAlgHom_target e }

end DimensionFourDependence
