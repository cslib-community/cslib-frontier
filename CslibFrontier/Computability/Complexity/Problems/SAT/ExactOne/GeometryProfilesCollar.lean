/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.SAT.ExactOne.GeometryProfilesPrefixData
public import CslibFrontier.Computability.Complexity.Problems.SAT.ExactOne.GeometryProfiles
public import CslibFrontier.Computability.Complexity.Problems.SAT.ExactOne.GeometryCollarGlue

/-!
# Collared positive exact-one profiles

The twenty-four ordered injections into the four exterior directions are handled by the common
annular collars. All geometry proofs reuse the fifteen inner-profile certificates and the
twenty-four collar certificates; they do not repeat an exhaustive route-pair audit for every
combination.

## Main results

* `collaredProfile_incidence_orthogonal`, `collaredProfile_incidence_isSimple`: actual placed
  incidence routes remain proper and continuously simple.

## References

These are original continuous gluing certificates for the exact-one replacement profiles.
-/

@[expose] public section

namespace Cslib.Complexity.SAT.ExactOne

open Orthogonal

/-- Every source endpoint of the actual inner prefix is its indexed north, west or east port. -/
theorem profile_prefix_terminal_endpoint (p : ClauseProfile) :
    ∀ v ∈ (profilePrefixGeometry p).terminalVariables,
      (profilePrefixGeometry p).variablePosition v =
        innerTemplatePort (terminalIndex (profilePrefixGeometry p) v) := by
  fin_cases p <;> decide +kernel

/-- Distinct exposed source variables have distinct collar indices. -/
theorem profile_prefix_terminalIndex_injective (p : ClauseProfile) :
    ∀ v ∈ (profilePrefixGeometry p).terminalVariables,
      ∀ w ∈ (profilePrefixGeometry p).terminalVariables,
        terminalIndex (profilePrefixGeometry p) v =
          terminalIndex (profilePrefixGeometry p) w → v = w := by
  fin_cases p <;> decide +kernel

/-- Every source placeholder has a valid local variable index. -/
theorem profile_prefix_terminal_lt (p : ClauseProfile) :
    ∀ v ∈ (profilePrefixGeometry p).terminalVariables,
      v < (profilePrefixGeometry p).variablePositions.length := by
  fin_cases p <;> decide +kernel

/-- Every listed variable of the inner template lies in its closed square. -/
theorem profile_prefix_variable_bounds (p : ClauseProfile) :
    ∀ v : Fin (profilePrefixGeometry p).variablePositions.length,
      let q := (profilePrefixGeometry p).variablePosition v
      0 ≤ q.1 ∧ q.1 ≤ 180000 ∧ 0 ≤ q.2 ∧ q.2 ≤ 180000 := by
  fin_cases p <;> decide +kernel

/-- An auxiliary variable never occupies a source boundary port. -/
theorem profile_prefix_auxiliary_ne_terminal (p : ClauseProfile) :
    ∀ v : Fin (profilePrefixGeometry p).variablePositions.length,
      v.val ∉ (profilePrefixGeometry p).terminalVariables →
        ∀ w ∈ (profilePrefixGeometry p).terminalVariables,
          (profilePrefixGeometry p).variablePosition v ≠
            (profilePrefixGeometry p).variablePosition w := by
  fin_cases p <;> decide +kernel

/-- Every listed clause position lies in the inner template's closed square. -/
theorem profile_prefix_clause_bounds (p : ClauseProfile) :
    ∀ i : Fin (profilePrefixGeometry p).clausePositions.length,
      let q := (profilePrefixGeometry p).clausePosition i
      0 ≤ q.1 ∧ q.1 ≤ 180000 ∧ 0 ≤ q.2 ∧ q.2 ≤ 180000 := by
  fin_cases p <;> decide +kernel

/-- All listed incidence points lie in the inner square, independently of the expensive
continuous pair-contact certificate. -/
theorem profile_prefix_incidence_points_bounds (p : ClauseProfile) :
    ∀ e ∈ (profilePrefixGeometry p).incidenceRoutes,
      ∀ q ∈ e.route, 0 ≤ q.1 ∧ q.1 ≤ 180000 ∧ 0 ≤ q.2 ∧ q.2 ≤ 180000 := by
  fin_cases p <;> decide +kernel

/-- No clause vertex occupies a source boundary port. -/
theorem profile_prefix_clause_ne_terminal (p : ClauseProfile) :
    ∀ i : Fin (profilePrefixGeometry p).clausePositions.length,
      ∀ w ∈ (profilePrefixGeometry p).terminalVariables,
        (profilePrefixGeometry p).clausePosition i ≠
          (profilePrefixGeometry p).variablePosition w := by
  fin_cases p <;> decide +kernel

/-- Each source placeholder belongs to exactly one local incidence. -/
theorem profile_prefix_terminal_unique (p : ClauseProfile) :
    ∀ e ∈ (profilePrefixGeometry p).incidenceRoutes,
      e.variableIndex ∈ (profilePrefixGeometry p).terminalVariables →
        ∀ f ∈ (profilePrefixGeometry p).incidenceRoutes,
          e.variableIndex = f.variableIndex → e = f := by
  fin_cases p <;> decide +kernel

/-- Two different incidences can share only an actual auxiliary variable, never a source
placeholder that will be removed by the global drawing compiler. -/
theorem profile_prefix_shared_variable_not_terminal (p : ClauseProfile)
    {e f : LocalIncidence} (he : e ∈ (profilePrefixGeometry p).incidenceRoutes)
    (hf : f ∈ (profilePrefixGeometry p).incidenceRoutes) (hne : e ≠ f)
    (hv : e.variableIndex = f.variableIndex) :
    e.variableIndex ∉ (profilePrefixGeometry p).terminalVariables := by
  intro ht
  exact hne (profile_prefix_terminal_unique p e he ht f hf hv)

/-- The finite route actually used by the collared incidence constructor. -/
def profileCollarRoute (p : ClauseProfile) (s : PortAssignment) (e : LocalIncidence) : Route :=
  if e.variableIndex ∈ (profilePrefixGeometry p).terminalVariables then
    collarPrefixRoute s (terminalIndex (profilePrefixGeometry p) e.variableIndex) e.route
  else collarRoute (collarReflected s) e.route

/-- Every actual inner prefix lies in the common side-180000 square. -/
theorem profile_prefix_incidence_bounds (p : ClauseProfile)
    (h : LocalGeometry.PrefixCheck (profilePrefixGeometry p))
    {e : LocalIncidence} (he : e ∈ (profilePrefixGeometry p).incidenceRoutes) :
    ∀ q ∈ e.route, 0 ≤ q.1 ∧ q.1 ≤ 180000 ∧ 0 ≤ q.2 ∧ q.2 ≤ 180000 := by
  have hsize : (profilePrefixGeometry p).size = 180000 :=
    (profileGeometry_costs p).2.2
  simpa only [hsize, Nat.cast_ofNat] using LocalGeometry.prefix_incidence_bounds h he

private theorem profile_prefix_terminal_last (p : ClauseProfile)
    (h : LocalGeometry.PrefixCheck (profilePrefixGeometry p)) {e : LocalIncidence}
    (he : e ∈ (profilePrefixGeometry p).incidenceRoutes)
    (ht : e.variableIndex ∈ (profilePrefixGeometry p).terminalVariables) :
    e.route.getLast? =
      some (innerTemplatePort (terminalIndex (profilePrefixGeometry p) e.variableIndex)) := by
  have hend := (LocalGeometry.prefix_incidence_endpoints h he).2.2.2
  rwa [profile_prefix_terminal_endpoint p e.variableIndex ht] at hend

/-- The actual collared incidence routes are properly orthogonal in every ordered port
assignment. The profile certificate is supplied separately to keep the data compiler lightweight.
-/
theorem collaredProfile_incidence_orthogonal (p : ClauseProfile)
    (h : LocalGeometry.PrefixCheck (profilePrefixGeometry p))
    {s : PortAssignment} (hs : s.Distinct) {e : LocalIncidence}
    (he : e ∈ (collaredPrefixGeometry (profilePrefixGeometry p) s).incidenceRoutes) :
    IsOrthogonal e.route := by
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
  dsimp only [LocalIncidence.route]
  split_ifs with ht
  · exact isOrthogonal_collarPrefixRoute hs (profile_prefix_terminal_last p h hf ht)
      (LocalGeometry.prefix_incidence_orthogonal h hf)
  · exact isOrthogonal_collarRoute _ (LocalGeometry.prefix_incidence_orthogonal h hf)

/-- The actual collared incidence routes are simple over their full real support. -/
theorem collaredProfile_incidence_isSimple (p : ClauseProfile)
    (h : LocalGeometry.PrefixCheck (profilePrefixGeometry p))
    {s : PortAssignment} (hs : s.Distinct) {e : LocalIncidence}
    (he : e ∈ (collaredPrefixGeometry (profilePrefixGeometry p) s).incidenceRoutes) :
    IsSimple e.route := by
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
  dsimp only [LocalIncidence.route]
  split_ifs with ht
  · exact isSimple_collarPrefixRoute hs (profile_prefix_terminal_last p h hf ht)
      (LocalGeometry.prefix_incidence_isSimple h hf) (profile_prefix_incidence_bounds p h hf)
  · exact isSimple_collarRoute _ (LocalGeometry.prefix_incidence_isSimple h hf)

private theorem profile_collar_core_contact (p : ClauseProfile)
    (h : LocalGeometry.PrefixCheck (profilePrefixGeometry p))
    {s : PortAssignment} {e f : LocalIncidence}
    (he : e ∈ (profilePrefixGeometry p).incidenceRoutes)
    (hf : f ∈ (profilePrefixGeometry p).incidenceRoutes) (hne : e ≠ f)
    {z : ℝ × ℝ} (hz : z ∈ support (collarRoute (collarReflected s) e.route))
    (hw : z ∈ support (collarRoute (collarReflected s) f.route)) :
    ∃ q ∈ (profilePrefixGeometry p).commonEndpoints e f,
      z = collarReal (collarReflected s) (realPoint q) := by
  rw [support_collarRoute] at hz hw
  obtain ⟨x, hx, hxz⟩ := hz
  obtain ⟨y, hy, hyz⟩ := hw
  have hxy := collarReal_injective (collarReflected s) (hxz.trans hyz.symm)
  subst y
  obtain ⟨q, hq, hxq⟩ := LocalGeometry.prefix_routes_contact h he hf hne hx hy
  exact ⟨q, hq, hxz.symm.trans (congrArg (collarReal (collarReflected s)) hxq)⟩

private theorem innerTemplatePort_not_mem_support (p : ClauseProfile)
    (h : LocalGeometry.PrefixCheck (profilePrefixGeometry p)) {e : LocalIncidence}
    (he : e ∈ (profilePrefixGeometry p).incidenceRoutes) {v : ℕ}
    (ht : v ∈ (profilePrefixGeometry p).terminalVariables) (hv : v ≠ e.variableIndex) :
    realPoint (innerTemplatePort (terminalIndex (profilePrefixGeometry p) v)) ∉ support e.route :=
  profile_prefix_terminal_endpoint p v ht ▸ LocalGeometry.prefix_variable_not_mem_support h he
    (v := ⟨v, profile_prefix_terminal_lt p v ht⟩) hv

private theorem profile_collar_connector_disjoint (p : ClauseProfile)
    (h : LocalGeometry.PrefixCheck (profilePrefixGeometry p))
    {s : PortAssignment} {e f : LocalIncidence}
    (he : e ∈ (profilePrefixGeometry p).incidenceRoutes)
    (ht : f.variableIndex ∈ (profilePrefixGeometry p).terminalVariables)
    (hv : f.variableIndex ≠ e.variableIndex) :
    Disjoint (support (collarRoute (collarReflected s) e.route))
      (support ((collarRoutes s).getD
        (terminalIndex (profilePrefixGeometry p) f.variableIndex) [])) :=
  disjoint_collarRoute_connector (profile_prefix_incidence_bounds p h he)
    (innerTemplatePort_not_mem_support p h he ht hv)

/-- The annular connectors introduce no new contacts between different incidence routes.
Every contact is the common affine placement of an original permitted local endpoint. -/
theorem profileCollarRoute_contact (p : ClauseProfile)
    (h : LocalGeometry.PrefixCheck (profilePrefixGeometry p))
    {s : PortAssignment} (hs : s.Distinct) {e f : LocalIncidence}
    (he : e ∈ (profilePrefixGeometry p).incidenceRoutes)
    (hf : f ∈ (profilePrefixGeometry p).incidenceRoutes) (hne : e ≠ f)
    {z : ℝ × ℝ} (hz : z ∈ support (profileCollarRoute p s e))
    (hw : z ∈ support (profileCollarRoute p s f)) :
    ∃ q ∈ (profilePrefixGeometry p).commonEndpoints e f,
      z = collarReal (collarReflected s) (realPoint q) := by
  have hve (ht : e.variableIndex ∈ (profilePrefixGeometry p).terminalVariables) :
      e.variableIndex ≠ f.variableIndex :=
    fun hv => profile_prefix_shared_variable_not_terminal p he hf hne hv ht
  have hvf (ht : f.variableIndex ∈ (profilePrefixGeometry p).terminalVariables) :
      f.variableIndex ≠ e.variableIndex :=
    fun hv => profile_prefix_shared_variable_not_terminal p hf he hne.symm hv ht
  unfold profileCollarRoute at hz hw
  split_ifs at hz with hte <;> split_ifs at hw with htf
  · have hidx : terminalIndex (profilePrefixGeometry p) e.variableIndex ≠
        terminalIndex (profilePrefixGeometry p) f.variableIndex := fun heq =>
      hve hte (profile_prefix_terminalIndex_injective p e.variableIndex hte f.variableIndex htf heq)
    obtain ⟨q, hqe, hqf, hzq⟩ := collarPrefixRoute_contact hs hidx
      (profile_prefix_terminal_last p h he hte) (profile_prefix_terminal_last p h hf htf)
      (profile_prefix_incidence_bounds p h he) (profile_prefix_incidence_bounds p h hf)
      (innerTemplatePort_not_mem_support p h he htf (hvf htf))
      (innerTemplatePort_not_mem_support p h hf hte (hve hte)) hz hw
    obtain ⟨a, ha, hqa⟩ := LocalGeometry.prefix_routes_contact h he hf hne hqe hqf
    exact ⟨a, ha, hzq.trans (congrArg (collarReal (collarReflected s)) hqa)⟩
  · rw [support_collarPrefixRoute hs (profile_prefix_terminal_last p h he hte)] at hz
    exact hz.elim (fun hz => profile_collar_core_contact p h he hf hne hz hw)
      (fun hz => False.elim (Set.disjoint_left.mp
        (profile_collar_connector_disjoint p h hf hte (hve hte)) hw hz))
  · rw [support_collarPrefixRoute hs (profile_prefix_terminal_last p h hf htf)] at hw
    exact hw.elim (fun hw => profile_collar_core_contact p h he hf hne hz hw)
      (fun hw => False.elim (Set.disjoint_left.mp
        (profile_collar_connector_disjoint p h he htf (hvf htf)) hz hw))
  · exact profile_collar_core_contact p h he hf hne hz hw

private theorem profileCollarRoute_corePoint_not_mem_support (p : ClauseProfile)
    (h : LocalGeometry.PrefixCheck (profilePrefixGeometry p))
    {s : PortAssignment} (hs : s.Distinct) {e : LocalIncidence}
    (he : e ∈ (profilePrefixGeometry p).incidenceRoutes) {q : Point}
    (hqb : 0 ≤ q.1 ∧ q.1 ≤ 180000 ∧ 0 ≤ q.2 ∧ q.2 ≤ 180000)
    (hne : e.variableIndex ∈ (profilePrefixGeometry p).terminalVariables →
      q ≠ (profilePrefixGeometry p).variablePosition e.variableIndex)
    (hn : realPoint q ∉ support e.route) :
    realPoint (collarPoint (collarReflected s) q) ∉ support (profileCollarRoute p s e) := by
  unfold profileCollarRoute
  split_ifs with hsource
  · refine collarPrefixRoute_not_mem_corePoint hs (profile_prefix_terminal_last p h he hsource)
      hqb ?_ hn
    rw [← profile_prefix_terminal_endpoint p e.variableIndex hsource]
    exact hne hsource
  · rw [realPoint_collarPoint]
    exact fun hp => hn ((mem_support_collarRoute_iff _ _ _).mp hp)

/-- A collared incidence avoids every nonincident actual auxiliary vertex. -/
theorem profileCollarRoute_auxiliary_not_mem_support (p : ClauseProfile)
    (h : LocalGeometry.PrefixCheck (profilePrefixGeometry p))
    {s : PortAssignment} (hs : s.Distinct) {e : LocalIncidence}
    (he : e ∈ (profilePrefixGeometry p).incidenceRoutes)
    (v : Fin (profilePrefixGeometry p).variablePositions.length)
    (ht : v.val ∉ (profilePrefixGeometry p).terminalVariables) (hv : v.val ≠ e.variableIndex) :
    realPoint (collarPoint (collarReflected s) ((profilePrefixGeometry p).variablePosition v)) ∉
      support (profileCollarRoute p s e) :=
  profileCollarRoute_corePoint_not_mem_support p h hs he (profile_prefix_variable_bounds p v)
    (fun hs' => profile_prefix_auxiliary_ne_terminal p v ht e.variableIndex hs')
    (LocalGeometry.prefix_variable_not_mem_support h he (v := v) hv)

/-- A collared incidence avoids every nonincident actual clause vertex. -/
theorem profileCollarRoute_clause_not_mem_support (p : ClauseProfile)
    (h : LocalGeometry.PrefixCheck (profilePrefixGeometry p))
    {s : PortAssignment} (hs : s.Distinct) {e : LocalIncidence}
    (he : e ∈ (profilePrefixGeometry p).incidenceRoutes)
    (i : Fin (profilePrefixGeometry p).clausePositions.length) (hi : i.val ≠ e.clauseIndex) :
    realPoint (collarPoint (collarReflected s) ((profilePrefixGeometry p).clausePosition i)) ∉
      support (profileCollarRoute p s e) :=
  profileCollarRoute_corePoint_not_mem_support p h hs he (profile_prefix_clause_bounds p i)
    (fun hs' => profile_prefix_clause_ne_terminal p i e.variableIndex hs')
    (LocalGeometry.prefix_clause_not_mem_support h he (i := i) hi)

/-- A collared incidence avoids every other exposed source endpoint. -/
theorem profileCollarRoute_source_not_mem_support (p : ClauseProfile)
    (h : LocalGeometry.PrefixCheck (profilePrefixGeometry p))
    {s : PortAssignment} (hs : s.Distinct) {e : LocalIncidence}
    (he : e ∈ (profilePrefixGeometry p).incidenceRoutes) {v : ℕ}
    (ht : v ∈ (profilePrefixGeometry p).terminalVariables) (hv : v ≠ e.variableIndex) :
    realPoint (collarOuterPort (s.side (terminalIndex (profilePrefixGeometry p) v))) ∉
      support (profileCollarRoute p s e) := by
  let i := terminalIndex (profilePrefixGeometry p) v
  obtain ⟨_, hr⟩ := List.head?_eq_some_iff.mp ((collar_check s hs).2 i).1
  have hsupp : realPoint (collarOuterPort (s.side i)) ∈
      support ((collarRoutes s).getD i []) := Or.inl ⟨_, hr ▸ List.mem_cons_self, rfl⟩
  have hd : Disjoint (support (collarRoute (collarReflected s) e.route))
      (support ((collarRoutes s).getD i [])) :=
    disjoint_collarRoute_connector (profile_prefix_incidence_bounds p h he)
      (innerTemplatePort_not_mem_support p h he ht hv)
  intro hp
  unfold profileCollarRoute at hp
  split_ifs at hp with heterm
  · rw [support_collarPrefixRoute hs (profile_prefix_terminal_last p h he heterm)] at hp
    rcases hp with hp | hp
    · exact Set.disjoint_left.mp hd hp hsupp
    · have hi : terminalIndex (profilePrefixGeometry p) e.variableIndex ≠ i := fun hi =>
        hv (profile_prefix_terminalIndex_injective p e.variableIndex heterm v ht hi).symm
      exact Set.disjoint_left.mp (collar_disjoint hs hi) hp hsupp
  · exact Set.disjoint_left.mp hd hp hsupp

/-- A collared route can touch the complete outer perimeter only at its own source endpoint;
an incidence to an internal auxiliary never touches that perimeter. -/
theorem profileCollarRoute_outer_boundary_contact (p : ClauseProfile)
    (h : LocalGeometry.PrefixCheck (profilePrefixGeometry p))
    {s : PortAssignment} (hs : s.Distinct) {e : LocalIncidence}
    (he : e ∈ (profilePrefixGeometry p).incidenceRoutes)
    {z : ℝ × ℝ} (hz : z ∈ support (profileCollarRoute p s e))
    (hb : z ∈ support collarBoundaryRoute) :
    e.variableIndex ∈ (profilePrefixGeometry p).terminalVariables ∧
      z = realPoint
        (collarOuterPort (s.side (terminalIndex (profilePrefixGeometry p) e.variableIndex))) := by
  unfold profileCollarRoute at hz
  split_ifs at hz with ht
  · exact ⟨ht, collarPrefixRoute_outer_boundary_contact hs (profile_prefix_terminal_last p h he ht)
      (profile_prefix_incidence_bounds p h he) hz hb⟩
  · have hcheck : routeBoxContactCheck [] collarBoundaryRoute (270000, 270000) 90000 =
        true := by decide +kernel
    obtain ⟨q, hq, _⟩ := routeBoxContactCheck_sound hcheck hb
      (collarRoute_in_innerBox _ (profile_prefix_incidence_bounds p h he) hz)
    exact False.elim (List.not_mem_nil hq)

/-- If every point of a route lies in the `180000`-by-`180000` inner square, then every point of
its collared route lies in the `540000`-by-`540000` outer square. -/
theorem collarRoute_points_bounds (reflected : Bool) {r : Route}
    (hr : ∀ q ∈ r, 0 ≤ q.1 ∧ q.1 ≤ 180000 ∧ 0 ≤ q.2 ∧ q.2 ≤ 180000) :
    ∀ q ∈ collarRoute reflected r,
      0 ≤ q.1 ∧ q.1 ≤ 540000 ∧ 0 ≤ q.2 ∧ q.2 ≤ 540000 := by
  intro q hq
  rw [collarRoute_eq_map] at hq
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hq
  have hb := hr a ha
  cases reflected <;> dsimp [collarPoint, collarOffset, mirrorPoint] <;> omega

end Cslib.Complexity.SAT.ExactOne
