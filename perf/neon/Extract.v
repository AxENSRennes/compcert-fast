(* Isolated executable test model; does not modify CompCert extraction. *)
From Coq Require Import Extraction ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlZBigInt.
From compcert.aarch64 Require Import Neon.
Extraction "perf/artifacts/neon/neon_model.ml"
  lane_bits lanes modulus normalize eval_lane scalar_loop eval_vector
  plan_for validate_plan checked_plan execute_plan vectorize
  instruction_supported compile_loop compile_plan run_compiled.
