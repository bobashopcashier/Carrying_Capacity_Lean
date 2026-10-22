import CarryingCapacity.MomentGeometry
import CarryingCapacity.Transport
import CarryingCapacity.Framework
import CarryingCapacity.RateControl
import CarryingCapacity.FiniteGenerator
import CarryingCapacity.Freezing
import CarryingCapacity.Models
import CarryingCapacity.ModelTransport
import CarryingCapacity.QuadraticModel
import CarryingCapacity.LimitArguments

/-!
# Checked foundations for carrying-capacity mean-field models

This is a partial formalization of DeWitt--Evans--Hiesmayr--Hummel (2024)
and Kenny Xie's moment-feedback manuscript. All imported theorems are proved.
The process-level existence, nonlinear-flow, mean-field, and chaos theorems
remain open; see README.md and docs/PAPER_MAP.md for exact coverage.
-/
