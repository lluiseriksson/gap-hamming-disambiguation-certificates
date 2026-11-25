import Lake
open Lake DSL

package «GapHammingDisambig» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib «GapHammingDisambig» where
  roots := #[`GapHammingDisambig]
