import RoboLean.Dynamics.RigidBodyInertia

/-!
# The generalized inertia under a change of body frame: Chapter 4 Exercise 3

MLS Chapter 4, Exercise 3, printed p. 208: "Show that under a change of body coordinate frame from
`B` to `C`, the generalized inertia matrix for a rigid body is given by
`𝓜_c = Ad_{g_bc}ᵀ 𝓜_b Ad_{g_bc} = [[m I, m R_bcᵀ p̂_bc R_bc], [−m R_bcᵀ p̂_bc R_bc, R_bcᵀ (𝓘 − m p̂_bc²) R_bc]]`,
where `g_bc` denotes the rigid motion taking `C` to `B`, and `𝓜_b` and `𝓜_c` are the generalized
inertia matrices expressed in frame `B` and frame `C`."

**Formalized.** For `𝓜_b = [[m I, 0], [0, 𝓘]]` of eq. (4.9) (body frame `B` at the mass center) and
any `g_bc = (R, p)`, the library's transformed inertia `Ad_gᵀ 𝓜 Ad_g` (`RigidBody.transformInertia`,
eq. (4.28), p. 176) is the printed block matrix (`transformInertia_generalizedInertia`); with
`R = I` it is the pure-translation form already in the library (`transformInertia_translation`).
Twist order `(v, ω)`, the linear block first, as printed. Nothing here concerns a physical body.
-/

noncomputable section

open Matrix

namespace RoboLean
namespace RigidBody

/-- **MLS Chapter 4, Exercise 3, p. 208: the generalized inertia in a second body frame.** For a
rigid body with mass `m` and inertia tensor `𝓘` in a body frame `B` at the mass center and a second
body frame `C` with `g_bc = (R, p)`, `Ad_{g_bc}ᵀ [[m I, 0], [0, 𝓘]] Ad_{g_bc}` is
`[[m I, m Rᵀ p̂ R], [−m Rᵀ p̂ R, Rᵀ (𝓘 − m p̂²) R]]`, exactly as printed. Twist order `(v, ω)`. -/
theorem transformInertia_generalizedInertia (g : RigidTransform) (m : ℝ)
    (𝓘 : Matrix (Fin 3) (Fin 3) ℝ) :
    transformInertia g (generalizedInertia m 𝓘) =
      Matrix.fromBlocks (m • (1 : Matrix (Fin 3) (Fin 3) ℝ))
        (m • (g.rotation.valᵀ * Vec3.hat g.translation * g.rotation.val))
        (-(m • (g.rotation.valᵀ * Vec3.hat g.translation * g.rotation.val)))
        (g.rotation.valᵀ * (𝓘 - m • (Vec3.hat g.translation * Vec3.hat g.translation)) *
          g.rotation.val) := by
  have hR : g.rotation.valᵀ * g.rotation.val = 1 := Rotation.transpose_mul g.rotation
  simp only [transformInertia, generalizedInertia, Twist.adjointMatrix,
    Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.transpose_mul,
    Vec3.hat_transpose, Matrix.transpose_zero, Matrix.mul_zero, Matrix.zero_mul, add_zero,
    zero_add]
  rw [Matrix.fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hR]
  · simp only [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_assoc]
  · simp only [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_neg, Matrix.neg_mul,
      Matrix.mul_assoc, smul_neg]
  · simp only [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_neg, Matrix.neg_mul,
      Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, smul_neg]
    abel

end RigidBody
end RoboLean
