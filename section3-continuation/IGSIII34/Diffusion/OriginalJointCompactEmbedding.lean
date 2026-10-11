import IGSIII34.Diffusion.ExtendedJointCompactDistance

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section

/-- Original decorated spaces embed isometrically into the comparison space
that also allows a path in a larger compact ambient. -/
def originalJointCompactSpaceToExtended : OriginalJointCompactSpace → ExtendedJointCompactSpace :=
  SeparationQuotient.lift
    (fun representative => extendedJointCompactClass (.ofOriginal representative))
    (fun first last equality => by
      apply eq_of_dist_eq_zero
      rw [extendedJointCompactClass_dist, extendedJointCompactDistance_ofOriginal]
      exact Metric.inseparable_iff.mp equality)

@[simp] theorem originalJointCompactSpaceToExtended_class
    (representative : OriginalJointCompactRepresentative) :
    originalJointCompactSpaceToExtended (originalJointCompactClass representative) =
      extendedJointCompactClass (.ofOriginal representative) := rfl

theorem originalJointCompactSpaceToExtended_isometry :
    Isometry originalJointCompactSpaceToExtended := by
  apply Isometry.of_dist_eq
  intro first last
  obtain ⟨first, rfl⟩ := SeparationQuotient.surjective_mk first
  obtain ⟨last, rfl⟩ := SeparationQuotient.surjective_mk last
  exact extendedJointCompactDistance_ofOriginal first last

end
end IGSIII34.Diffusion
