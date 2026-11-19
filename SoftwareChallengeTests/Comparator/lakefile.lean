import Lake
open Lake DSL

package «comparator_cases» where
  leanOptions := #[⟨`autoImplicit, false⟩]

lean_lib «Challenge» where
  leanOptions := #[⟨`warn.sorry, false⟩]

@[default_target]
lean_lib «Cases» where
  roots := #[`Cases.Solution, `Cases.Elsewhere, `Cases.Forged]

lean_lib «Broken» where
  roots := #[`Cases.Broken]
