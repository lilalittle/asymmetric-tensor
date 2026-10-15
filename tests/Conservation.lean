import AsymmetricTensor

open AsymmetricTensor

example (A : T2) : CoordinateConserved (fun _ => A) :=
  constant_coordinate_conserved A

example : ¬ CoordinateConserved (fun x _ _ => x 0) :=
  coordinate_field_not_conserved

example (U : MetricField) (hU : CoordinateConserved U) (x : SpaceTime) :
    metric_divergence U x 0 = 0 :=
  bernoulli_energy_conservation U hU x

#print axioms constant_coordinate_conserved
#print axioms exists_coordinate_conserved
#print axioms coordinate_field_not_conserved
#print axioms bernoulli_energy_conservation
#print axioms navier_stokes_momentum_conservation
#print axioms geometric_navier_stokes
#print axioms unified_action_separation
