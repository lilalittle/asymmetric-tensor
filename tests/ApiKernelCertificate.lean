import Lean

/-! Negative controls for the kernel certificate used by the raw API comparison.
The certificate checks an existing constant at a supplied full reference type.
It adds nothing to the production environment and cannot insert a fallback axiom.
-/

open Lean Elab Command

run_cmd do
  let kernel := (← getEnv).toKernelEnv
  let options := (← getOptions).setBool `debug.skipKernelTC false
  let certificate (name : Name) (type value : Expr) :=
    kernel.addDecl options (.defnDecl {
      name := name
      levelParams := []
      type := type
      value := value
      hints := .opaque
      safety := .safe
    })
  match certificate `CertificateControls.valid (mkConst ``True) (mkConst ``True.intro) with
  | .ok _ => pure ()
  | .error _ => throwError "KERNEL_CERTIFICATE_CONTROL: valid type rejected"
  match certificate `CertificateControls.changedProposition
      (mkConst ``False) (mkConst ``True.intro) with
  | .error _ => pure ()
  | .ok _ => throwError "KERNEL_CERTIFICATE_CONTROL: changed proposition accepted"
  match certificate `CertificateControls.changedDataType
      (mkConst ``Nat) (mkConst ``True.intro) with
  | .error _ => pure ()
  | .ok _ => throwError "KERNEL_CERTIFICATE_CONTROL: changed data type accepted"
  logInfo "KERNEL_CERTIFICATE_CONTROLS_OK: valid cast passes, both type mutants rejected"
