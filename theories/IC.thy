theory IC
  imports "HOL-Library.AList"
begin

(* Partial maps *)

typedef ('a, 'b) list_map = "{f :: ('a \<times> 'b) list. distinct (map fst f)}"
  by (auto intro: exI[of _ "[]"])

setup_lifting type_definition_list_map

lift_bnf (dead 'k, set: 'v) list_map [wits: "[] :: ('k \<times> 'v) list"] for map: map rel: rel
  by auto

hide_const (open) map set rel

lift_definition list_map_dom :: "('a, 'b) list_map \<Rightarrow> 'a set" is
  "set \<circ> map fst" .

lift_definition list_map_vals :: "('a, 'b) list_map \<Rightarrow> 'b list" is
  "map snd" .

lift_definition list_map_range :: "('a, 'b) list_map \<Rightarrow> 'b set" is
  "set \<circ> map snd" .

lift_definition list_map_sum_vals :: "('b \<Rightarrow> nat) \<Rightarrow> ('a, 'b) list_map \<Rightarrow> nat" is
  "\<lambda>g. sum_list \<circ> (map (g \<circ> snd))" .

lift_definition list_map_get :: "('a, 'b) list_map \<Rightarrow> 'a \<Rightarrow> 'b option" is
  "map_of" .

lemma list_map_get_dom[dest]: "x \<in> list_map_dom f \<Longrightarrow> list_map_get f x = None \<Longrightarrow> False"
  by transfer auto

lift_definition list_map_set :: "('a, 'b) list_map \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) list_map" is
  "\<lambda>f x y. AList.update x y f"
  by (rule distinct_update)

lift_definition list_map_del :: "('a, 'b) list_map \<Rightarrow> 'a \<Rightarrow> ('a, 'b) list_map" is
  "\<lambda>f x. AList.delete x f"
  by (rule distinct_delete)

lift_definition list_map_empty :: "('a, 'b) list_map" is "[]"
  by auto

lemma list_map_empty_dom[simp]: "list_map_dom list_map_empty = {}"
  by transfer auto

lift_definition list_map_init :: "('a \<times> 'b) list \<Rightarrow> ('a, 'b) list_map" is
  "\<lambda>xys. AList.updates (map fst xys) (map snd xys) []"
  using distinct_updates
  by force

lift_definition list_map_map :: "('b \<Rightarrow> 'c) \<Rightarrow> ('a, 'b) list_map \<Rightarrow> ('a, 'c) list_map" is
  "\<lambda>f xs. map (\<lambda>(k, v). (k, f v)) xs"
  by (auto simp: comp_def case_prod_beta)

lemma list_map_sum_vals_split: "(\<And>ctxt. ctxt \<in> list_map_range xs \<Longrightarrow> f (g ctxt) \<le> f ctxt) \<Longrightarrow> list_map_sum_vals f xs =
  list_map_sum_vals id
    (list_map_map (\<lambda>ctxt. if P ctxt then f ctxt - f (g ctxt) else 0) xs) +
  list_map_sum_vals f
    (list_map_map (\<lambda>ctxt. if P ctxt then g ctxt else ctxt) xs)"
  apply (transfer fixing: f g P)
  subgoal for xs
    by (induction xs) auto
  done

lemma list_map_sum_vals_filter:
  assumes "\<And>b. b \<in> list_map_range xs \<Longrightarrow> P b = None \<Longrightarrow> f b = 0" "\<And>b y. b \<in> list_map_range xs \<Longrightarrow> P b = Some y \<Longrightarrow> f b = g y"
  shows "list_map_sum_vals id (list_map_map f xs) = sum_list (map g (List.map_filter P (list_map_vals xs)))"
  using assms
  apply (transfer fixing: f g P)
  subgoal for xs
    by (induction xs) (auto simp: List.map_filter_def)
  done

lemma list_map_sum_in_ge_aux:
  fixes g :: "'a \<Rightarrow> nat"
  shows "distinct (map fst f) \<Longrightarrow> map_of f x = Some y \<Longrightarrow> g y \<le> sum_list (map g (map snd f))"
  by (induction f) (auto split: if_splits)

lemma list_map_sum_in_ge: "list_map_get f x = Some y \<Longrightarrow> list_map_sum_vals g f \<ge> g y"
  apply transfer
  using list_map_sum_in_ge_aux[OF _ map_of_is_SomeI]
  by fastforce

lemma list_map_sum_in_aux: fixes g :: "'a \<Rightarrow> nat"
  shows "distinct (map fst f) \<Longrightarrow> map_of f x = Some y \<Longrightarrow>
  sum_list (map (g \<circ> snd) (AList.update x y' f)) = sum_list (map (g \<circ> snd) f) + g y' - g y"
  apply (induction f)
   apply auto[1]
  subgoal for a f
    using list_map_sum_in_ge_aux[OF _ map_of_is_SomeI, of f x y g]
    by auto
  done

lemma list_map_sum_in: "list_map_get f x = Some y \<Longrightarrow> list_map_sum_vals g (list_map_set f x y') = list_map_sum_vals g f + g y' - g y"
  apply transfer
  using list_map_sum_in_aux
  by fastforce

lemma list_map_sum_out_aux:
  "x \<notin> set (map fst f) \<Longrightarrow> sum_list (map (g \<circ> snd) (AList.update x y f)) = sum_list (map (g \<circ> snd) f) + g y"
  by (induction f) (auto simp: add.assoc)

lemma list_map_sum_out: "x \<notin> list_map_dom f \<Longrightarrow> list_map_sum_vals g (list_map_set f x y) = list_map_sum_vals g f + g y"
  apply transfer
  using list_map_sum_out_aux
  by fastforce

lemma list_map_del_sum_aux:
  fixes g :: "'a \<Rightarrow> nat"
  shows "distinct (map fst f) \<Longrightarrow> map_of f x = Some y \<Longrightarrow> sum_list (map (g \<circ> snd) f) = sum_list (map (g \<circ> snd) (AList.delete x f)) + g y"
  by (induction f) auto

lemma list_map_del_sum: "list_map_get f x = Some y \<Longrightarrow> list_map_sum_vals g f = list_map_sum_vals g (list_map_del f x) + g y"
  apply transfer
  using list_map_del_sum_aux
  by fastforce

(* Abstract behaviour *)

(* Abstract canisters *)

type_synonym 'b arg = 'b
type_synonym 's method_name = 's

type_synonym timestamp = nat
datatype status = Running | Stopping | Stopped
record ('b) env =
  env_time :: timestamp
  balance :: nat
  freezing_limit :: nat
  certificate :: "'b option"
  status :: status

type_synonym reject_code = nat
datatype ('b, 's) response =
  Reply "'b"
| Reject reject_code 's
record ('p, 'canid, 's, 'b, 'c) method_call =
  callee :: 'canid
  method_name :: "'s method_name"
  arg :: 'b
  transferred_cycles :: nat
  callback :: 'c

record trap_return = cycles_used :: nat
record 'x cycles_return =
  return :: 'x
  cycles_used :: nat
record ('w, 'p, 'canid, 's, 'b, 'c) update_return =
  new_state :: 'w
  new_calls :: "('p, 'canid, 's, 'b, 'c) method_call list"
  new_certified_data :: "'b option"
  response :: "('b, 's) response option"
  cycles_accepted :: nat
  cycles_used :: nat
record ('b, 's) query_return =
  response :: "('b, 's) response"
  cycles_used :: nat
record 'w heartbeat_return =
  new_state :: 'w
  cycles_used :: nat
type_synonym ('w, 'p, 'canid, 's, 'b, 'c) update_func = "'w \<Rightarrow> trap_return + ('w, 'p, 'canid, 's, 'b, 'c) update_return"
type_synonym ('w, 'b, 's) query_func = "'w \<Rightarrow> trap_return + ('b, 's) query_return"
type_synonym 'w heartbeat_func = "'w \<Rightarrow> trap_return + 'w heartbeat_return"

type_synonym available_cycles = nat
type_synonym refunded_cycles = nat

datatype inspect_method_result = Accept | Reject
record ('p, 'canid, 'b, 'w, 'sm, 'c, 's) canister_module_rec =
  init :: "'canid \<times> 'b arg \<times> 'p \<times> 'b env \<Rightarrow> trap_return + 'w cycles_return"
  pre_upgrade :: "'w \<times> 'p \<times> 'b env \<Rightarrow> trap_return + 'sm cycles_return"
  post_upgrade :: "'canid \<times> 'sm \<times> 'b arg \<times> 'p \<times> 'b env \<Rightarrow> trap_return + 'w cycles_return"
  update_methods :: "('s, ('b arg \<times> 'p \<times> 'b env \<times> available_cycles) \<Rightarrow> ('w, 'p, 'canid, 's, 'b, 'c) update_func) list_map"
  query_methods :: "('s, ('b arg \<times> 'p \<times> 'b env) \<Rightarrow> ('w, 'b, 's) query_func) list_map"
  heartbeat :: "'b env \<Rightarrow> 'w heartbeat_func"
  callbacks :: "('c \<times> ('b, 's) response \<times> refunded_cycles \<times> 'b env \<times> available_cycles) \<Rightarrow> ('w, 'p, 'canid, 's, 'b, 'c) update_func"
  inspect_message :: "('s \<times> 'w \<times> 'b arg \<times> 'p \<times> 'b env) \<Rightarrow> trap_return + inspect_method_result cycles_return"
typedef ('p, 'canid, 'b, 'w, 'sm, 'c, 's) canister_module =
  "{m :: ('p, 'canid, 'b, 'w, 'sm, 'c, 's) canister_module_rec. list_map_dom (update_methods m) \<inter> list_map_dom (query_methods m) = {}}"
  by (auto intro: exI[of _ "\<lparr>init = undefined, pre_upgrade = undefined, post_upgrade = undefined,
      update_methods = list_map_empty, query_methods = list_map_empty, heartbeat = undefined, callbacks = undefined,
      inspect_message = undefined\<rparr>"])

setup_lifting type_definition_canister_module

lift_definition canister_module_init :: "('p, 'canid, 'b, 'w, 'sm, 'c, 's) canister_module \<Rightarrow> 'canid \<times> 'b arg \<times> 'p \<times> 'b env \<Rightarrow> trap_return + 'w cycles_return" is "init" .
lift_definition canister_module_pre_upgrade :: "('p, 'canid, 'b, 'w, 'sm, 'c, 's) canister_module \<Rightarrow> 'w \<times> 'p \<times> 'b env \<Rightarrow> trap_return + 'sm cycles_return" is pre_upgrade .
lift_definition canister_module_post_upgrade :: "('p, 'canid, 'b, 'w, 'sm, 'c, 's) canister_module \<Rightarrow> 'canid \<times> 'sm \<times> 'b arg \<times> 'p \<times> 'b env \<Rightarrow> trap_return + 'w cycles_return" is post_upgrade .
lift_definition canister_module_inspect_message :: "('p, 'canid, 'b, 'w, 'sm, 'c, 's) canister_module \<Rightarrow> ('s \<times> 'w \<times> 'b arg \<times> 'p \<times> 'b env) \<Rightarrow> trap_return + inspect_method_result cycles_return" is inspect_message .
lift_definition canister_module_update_methods :: "('p, 'canid, 'b, 'w, 'sm, 'c, 's) canister_module \<Rightarrow> ('s, ('b arg \<times> 'p \<times> 'b env \<times> available_cycles) \<Rightarrow> ('w, 'p, 'canid, 's, 'b, 'c) update_func) list_map" is update_methods .
lift_definition canister_module_query_methods :: "('p, 'canid, 'b, 'w, 'sm, 'c, 's) canister_module \<Rightarrow> ('s, ('b arg \<times> 'p \<times> 'b env) \<Rightarrow> ('w, 'b, 's) query_func) list_map" is query_methods .

lift_definition dispatch_method :: "'s \<Rightarrow> ('p, 'canid, 'b, 'w, 'sm, 'c, 's) canister_module \<Rightarrow>
  ((('b arg \<times> 'p \<times> 'b env \<times> available_cycles) \<Rightarrow> ('w, 'p, 'canid, 's, 'b, 'c) update_func) +
   (('b arg \<times> 'p \<times> 'b env) \<Rightarrow> ('w, 'b, 's) query_func)) option" is
  "\<lambda>f m. case list_map_get (update_methods m) f of Some f' \<Rightarrow> Some (Inl f') | None \<Rightarrow> (case list_map_get (query_methods m) f of Some f' \<Rightarrow> Some (Inr f') | None \<Rightarrow> None)" .

lift_definition canister_module_callbacks :: "('p, 'canid, 'b, 'w, 'sm, 'c, 's) canister_module \<Rightarrow>
  ('c \<times> ('b, 's) response \<times> refunded_cycles \<times> 'b env \<times> available_cycles) \<Rightarrow> ('w, 'p, 'canid, 's, 'b, 'c) update_func" is
  callbacks .

lift_definition canister_module_heartbeat :: "('p, 'canid, 'b, 'w, 'sm, 'c, 's) canister_module \<Rightarrow> 'b env \<Rightarrow> 'w heartbeat_func" is
  heartbeat .

(* Call contexts *)

record ('b, 'p, 'uid, 'canid, 's) request =
  nonce :: 'b
  ingress_expiry :: nat
  sender :: 'uid
  canister_id :: 'canid
  method_name :: 's
  arg :: 'b
datatype ('b, 'p, 'uid, 'canid, 's, 'c, 'cid) call_origin =
  From_user "('b, 'p, 'uid, 'canid, 's) request"
| From_canister "'cid" "'c"
| From_heartbeat
record ('p, 'uid, 'canid, 'b, 's, 'c, 'cid) call_ctxt_rep =
  canister :: 'canid
  origin :: "('b, 'p, 'uid, 'canid, 's, 'c, 'cid) call_origin"
  needs_to_respond :: bool
  deleted :: bool
  available_cycles :: nat

typedef ('p, 'uid, 'canid, 'b, 's, 'c, 'cid) call_ctxt = "{ctxt :: ('p, 'uid, 'canid, 'b, 's, 'c, 'cid) call_ctxt_rep.
  (deleted ctxt \<longrightarrow> \<not>needs_to_respond ctxt) \<and> (\<not>needs_to_respond ctxt \<longrightarrow> available_cycles ctxt = 0)}"
  by (auto intro: exI[of _ "\<lparr>canister = undefined, origin = undefined, needs_to_respond = True, deleted = False, available_cycles = 0\<rparr>"])

setup_lifting type_definition_call_ctxt

lift_definition call_ctxt_canister :: "('p, 'uid, 'canid, 'b, 's, 'c, 'cid) call_ctxt \<Rightarrow> 'canid" is "canister" .

lift_definition call_ctxt_origin :: "('p, 'uid, 'canid, 'b, 's, 'c, 'cid) call_ctxt \<Rightarrow> ('b, 'p, 'uid, 'canid, 's, 'c, 'cid) call_origin" is "origin" .

lift_definition call_ctxt_needs_to_respond :: "('p, 'uid, 'canid, 'b, 's, 'c, 'cid) call_ctxt \<Rightarrow> bool" is needs_to_respond .

lift_definition call_ctxt_deleted :: "('p, 'uid, 'canid, 'b, 's, 'c, 'cid) call_ctxt \<Rightarrow> bool" is deleted .

lift_definition call_ctxt_available_cycles :: "('p, 'uid, 'canid, 'b, 's, 'c, 'cid) call_ctxt \<Rightarrow> nat" is available_cycles .

lemma call_ctxt_not_needs_to_respond_available_cycles: "\<not>call_ctxt_needs_to_respond x2 \<Longrightarrow> call_ctxt_available_cycles x2 = 0"
  by transfer auto

lift_definition call_ctxt_respond :: "('p, 'uid, 'canid, 'b, 's, 'c, 'cid) call_ctxt \<Rightarrow> ('p, 'uid, 'canid, 'b, 's, 'c, 'cid) call_ctxt" is
  "\<lambda>ctxt. ctxt\<lparr>available_cycles := 0, needs_to_respond := False\<rparr>"
  by auto

lemma call_ctxt_respond_available_cycles[simp]: "call_ctxt_available_cycles (call_ctxt_respond ctxt) = 0"
  by transfer auto

lemma call_ctxt_respond_needs_to_respond[dest]: "call_ctxt_needs_to_respond (call_ctxt_respond ctxt) \<Longrightarrow> False"
  by transfer auto

lift_definition call_ctxt_deduct_cycles :: "nat \<Rightarrow> ('p, 'uid, 'canid, 'b, 's, 'c, 'cid) call_ctxt \<Rightarrow> ('p, 'uid, 'canid, 'b, 's, 'c, 'cid) call_ctxt" is
  "\<lambda>n ctxt. ctxt\<lparr>available_cycles := available_cycles ctxt - n\<rparr>"
  by auto

lemma call_ctxt_deduct_cycles_origin[simp]: "call_ctxt_origin (call_ctxt_deduct_cycles n ctxt) = call_ctxt_origin ctxt"
  by transfer auto

lemma call_ctxt_deduct_cycles_needs_to_respond[simp]: "call_ctxt_needs_to_respond (call_ctxt_deduct_cycles n ctxt) = call_ctxt_needs_to_respond ctxt"
  by transfer auto

lemma call_ctxt_deduct_cycles_available_cycles[simp]: "call_ctxt_available_cycles (call_ctxt_deduct_cycles n ctxt) = call_ctxt_available_cycles ctxt - n"
  by transfer auto

lift_definition call_ctxt_delete :: "('p, 'uid, 'canid, 'b, 's, 'c, 'cid) call_ctxt \<Rightarrow> ('p, 'uid, 'canid, 'b, 's, 'c, 'cid) call_ctxt" is
  "\<lambda>ctxt. ctxt\<lparr>deleted := True, needs_to_respond := False, available_cycles := 0\<rparr>"
  by auto

(* Calls and Messages *)

datatype 'canid queue_origin = System | Canister 'canid
datatype 'canid queue = Unordered | Queue "'canid queue_origin" 'canid
datatype ('s, 'p, 'b, 'c) entry_point =
  Public_method "'s method_name" "'p" "'b"
| Callback "'c" "('b, 's) response" "refunded_cycles"
| Heartbeat

datatype ('b, 'p, 'uid, 'canid, 's, 'c, 'cid) message =
  Call_message "('b, 'p, 'uid, 'canid, 's, 'c, 'cid) call_origin" 'p 'canid 's 'b nat "'canid queue"
| Func_message 'cid 'canid "('s, 'p, 'b, 'c) entry_point" "'canid queue"
| Response_message "('b, 'p, 'uid, 'canid, 's, 'c, 'cid) call_origin" "('b, 's) response" nat

(* API requests *)

type_synonym 'b path = "'b list"
record ('b, 'uid) StateRead =
  nonce :: 'b
  ingress_expiry :: nat
  sender :: 'uid
  paths :: "'b path list"
record ('b, 'uid, 'canid, 's) CanisterQuery =
  nonce :: 'b
  ingress_expiry :: nat
  sender :: 'uid
  canister_id :: 'canid
  method_name :: 's
  arg :: 'b
type_synonym ('b, 'uid, 'canid, 's) APIReadRequest = "('b, 'uid) StateRead + ('b, 'uid, 'canid, 's) CanisterQuery"
record ('b, 'p, 'uid, 'canid, 's, 'pk, 'sig, 'sd) envelope =
  content :: "('b, 'p, 'uid, 'canid, 's) request + ('b, 'uid, 'canid, 's) APIReadRequest"
  sender_pubkey :: "'pk option"
  sender_sig :: "'sig option"
  sender_delegation :: 'sd

datatype ('b, 's) request_status = Received | Processing | Rejected reject_code 's | Replied 'b | Done

(* The system state *)

record ('p, 'canid, 'b, 'w, 'sm, 'c, 's) can_state_rec =
  wasm_state :: 'w
  module :: "('p, 'canid, 'b, 'w, 'sm, 'c, 's) canister_module"
  raw_module :: 'b
  public_custom_sections :: "('s, 'b) list_map"
  private_custom_sections :: "('s, 'b) list_map"
type_synonym ('p, 'canid, 'b, 'w, 'sm, 'c, 's) can_state = "('p, 'canid, 'b, 'w, 'sm, 'c, 's) can_state_rec option"
datatype ('b, 'p, 'uid, 'canid, 's, 'c, 'cid) can_status = Running | Stopping "(('b, 'p, 'uid, 'canid, 's, 'c, 'cid) call_origin \<times> nat) list" | Stopped
record ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic =
  requests :: "(('b, 'p, 'uid, 'canid, 's) request, ('b, 's) request_status) list_map"
  canisters :: "('canid, ('p, 'canid, 'b, 'w, 'sm, 'c, 's) can_state) list_map"
  controllers :: "('canid,  'p set) list_map"
  freezing_threshold :: "('canid,  nat) list_map"
  canister_status :: "('canid,  ('b, 'p, 'uid, 'canid, 's, 'c, 'cid) can_status) list_map"
  time :: "('canid,  timestamp) list_map"
  balances :: "('canid,  nat) list_map"
  certified_data :: "('canid,  'b) list_map"
  system_time :: timestamp
  call_contexts :: "('cid, ('p, 'uid, 'canid, 'b, 's, 'c, 'cid) call_ctxt) list_map"
  messages :: "('b, 'p, 'uid, 'canid, 's, 'c, 'cid) message list"
  root_key :: 'pk

(* Candid *)

datatype ('s, 'b, 'p) candid = Candid_nat nat
  | Candid_text 's
  | Candid_blob (candid_unwrap_blob: 'b)
  | Candid_opt "('s, 'b, 'p) candid"
  | Candid_vec "('s, 'b, 'p) candid list"
  | Candid_record "('s, ('s, 'b, 'p) candid) list_map"
  | Candid_null
  | Candid_empty

fun candid_is_blob :: "('s, 'b, 'p) candid \<Rightarrow> bool" where
  "candid_is_blob (Candid_blob b) = True"
| "candid_is_blob _ = False"

fun candid_lookup :: "('s, 'b, 'p) candid \<Rightarrow> 's \<Rightarrow> ('s, 'b, 'p) candid option" where
  "candid_lookup (Candid_record m) s = list_map_get m s"
| "candid_lookup _ _ = None"

(* State transitions *)

context fixes
  CANISTER_ERROR :: reject_code
  and CANISTER_REJECT :: reject_code
  and SYS_FATAL :: reject_code
  and SYS_TRANSIENT :: reject_code
  and MAX_CYCLES_PER_MESSAGE :: nat
  and MAX_CYCLES_PER_RESPONSE :: nat
  and MAX_CANISTER_BALANCE :: nat
  and ic_freezing_limit :: "('p :: linorder, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> 'canid \<Rightarrow> nat"
  and ic_idle_cycles_burned_per_day :: "('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> 'canid \<Rightarrow> nat"
  and blob_length :: "'b \<Rightarrow> nat"
  and sha_256 :: "'b \<Rightarrow> 'b"
  and ic_principal :: 'canid
  and blob_of_candid :: "('s, 'b, 'p) candid \<Rightarrow> 'b"
  and parse_candid :: "'b \<Rightarrow> ('s, 'b, 'p) candid option"
  and parse_principal :: "'b \<Rightarrow> 'p option"
  and blob_of_principal :: "'p \<Rightarrow> 'b"
  and empty_blob :: 'b
  and is_system_assigned :: "'p \<Rightarrow> bool"
  and encode_string :: "string \<Rightarrow> 's"
  and principal_of_uid :: "'uid \<Rightarrow> 'p"
  and principal_of_canid :: "'canid \<Rightarrow> 'p"
  and canid_of_principal :: "'p \<Rightarrow> 'canid option"
  and parse_wasm_mod :: "'b \<Rightarrow> ('p, 'canid, 'b, 'w, 'sm, 'c, 's) canister_module option"
  and parse_public_custom_sections :: "'b \<Rightarrow> ('s, 'b) list_map option"
  and parse_private_custom_sections :: "'b \<Rightarrow> ('s, 'b) list_map option"
  and verify_envelope :: "('b, 'p, 'uid, 'canid, 's, 'pk, 'sig, 'sd) envelope \<Rightarrow> 'p \<Rightarrow> nat \<Rightarrow> 'p set" (* TODO *)
begin

(* Type conversion functions *)

definition canid_of_blob :: "'b \<Rightarrow> 'canid option" where
  "canid_of_blob b = (case parse_principal b of Some p \<Rightarrow> canid_of_principal p | _ \<Rightarrow> None)"

definition blob_of_canid :: "'canid \<Rightarrow> 'b" where
  "blob_of_canid = blob_of_principal \<circ> principal_of_canid"

(* Candid helper functions *)

definition candid_nested_lookup :: "'b \<Rightarrow> 's list \<Rightarrow> ('s, 'b, 'p) candid option" where
  "candid_nested_lookup b = foldl (\<lambda>c s. case c of Some c' \<Rightarrow> candid_lookup c' s | _ \<Rightarrow> None) (parse_candid b)"

definition candid_parse_controllers :: "'b \<Rightarrow> 'p set option" where
  "candid_parse_controllers b = (case candid_nested_lookup b [encode_string ''settings'', encode_string ''controllers''] of Some (Candid_vec xs) \<Rightarrow>
    if (\<forall>c'' \<in> set xs. candid_is_blob c'' \<and> parse_principal (candid_unwrap_blob c'') \<noteq> None) then
      Some (the ` parse_principal ` candid_unwrap_blob ` set xs)
    else None | _ \<Rightarrow> None)"

definition candid_parse_nat :: "'b \<Rightarrow> 's list \<Rightarrow> nat option" where
  "candid_parse_nat b s = (case candid_nested_lookup b s of Some (Candid_nat n') \<Rightarrow> Some n' | _ \<Rightarrow> None)"

definition candid_parse_text :: "'b \<Rightarrow> 's list \<Rightarrow> 's option" where
  "candid_parse_text b s = (case candid_nested_lookup b s of Some (Candid_text t') \<Rightarrow> Some t' | _ \<Rightarrow> None)"

definition candid_parse_blob :: "'b \<Rightarrow> 's list \<Rightarrow> 'b option" where
  "candid_parse_blob b s = (case candid_nested_lookup b s of Some (Candid_blob b') \<Rightarrow> Some b' | _ \<Rightarrow> None)"

definition candid_parse_cid :: "'b \<Rightarrow> 'canid option" where
  "candid_parse_cid b = (case candid_parse_blob b [encode_string ''canister_id''] of Some b' \<Rightarrow> canid_of_blob b' | _ \<Rightarrow> None)"

fun candid_of_status :: "status \<Rightarrow> ('s, 'b, 'p) candid" where
  "candid_of_status status.Running = Candid_text (encode_string ''Running'')"
| "candid_of_status status.Stopping = Candid_text (encode_string ''Stopping'')"
| "candid_of_status status.Stopped = Candid_text (encode_string ''Stopped'')"

(* Cycles *)

fun carried_cycles :: "('b, 'p, 'uid, 'canid, 's, 'c, 'cid) call_origin \<Rightarrow> nat" where
  "carried_cycles (From_canister _ _) = MAX_CYCLES_PER_RESPONSE"
| "carried_cycles _ = 0"

fun cycles_reserved :: "('s, 'p, 'b, 'c) entry_point \<Rightarrow> nat" where
  "cycles_reserved (entry_point.Public_method _ _ _) = MAX_CYCLES_PER_MESSAGE"
| "cycles_reserved (entry_point.Callback _ _ _) = MAX_CYCLES_PER_RESPONSE"
| "cycles_reserved (entry_point.Heartbeat) = MAX_CYCLES_PER_MESSAGE"

fun message_cycles :: "('b, 'p, 'uid, 'canid, 's, 'c, 'cid) message \<Rightarrow> nat" where
  "message_cycles (Call_message orig _ _ _ _ trans_cycles q) = carried_cycles orig + trans_cycles"
| "message_cycles (Func_message _ _ ep _) = cycles_reserved ep"
| "message_cycles (Response_message orig _ ref_cycles) = carried_cycles orig + ref_cycles"

fun status_cycles :: "('b, 'p, 'uid, 'canid, 's, 'c, 'cid) can_status \<Rightarrow> nat" where
  "status_cycles (Stopping os) = sum_list (map (carried_cycles \<circ> fst) os) + sum_list (map snd os)"
| "status_cycles _ = 0"

lift_definition call_ctxt_carried_cycles :: "('p, 'uid, 'canid, 'b, 's, 'c, 'cid) call_ctxt \<Rightarrow> nat" is
  "\<lambda>ctxt. (if needs_to_respond ctxt
    then available_cycles ctxt + carried_cycles (origin ctxt)
    else 0)" .

lemma call_ctxt_respond_carried_cycles[simp]: "call_ctxt_carried_cycles (call_ctxt_respond ctxt) = 0"
  by transfer auto

lemma call_ctxt_carried_cycles: "call_ctxt_carried_cycles ctxt = (if call_ctxt_needs_to_respond ctxt
  then call_ctxt_available_cycles ctxt + carried_cycles (call_ctxt_origin ctxt) else 0)"
  by transfer auto

lemma call_ctxt_delete_carried_cycles[simp]: "call_ctxt_carried_cycles (call_ctxt_delete ctxt) = 0"
  by transfer auto

definition total_cycles :: "('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> nat" where
  "total_cycles ic = (
    let cycles_in_balances = list_map_sum_vals id (balances ic) in
    let cycles_in_messages = sum_list (map message_cycles (messages ic)) in
    let cycles_in_contexts = list_map_sum_vals call_ctxt_carried_cycles (call_contexts ic) in
    let cycles_in_statuses = list_map_sum_vals status_cycles (canister_status ic) in
    cycles_in_balances + cycles_in_messages + cycles_in_contexts + cycles_in_statuses)"

(* Accessor functions *)

fun calling_context :: "('b, 'p, 'uid, 'canid, 's, 'c, 'cid) call_origin \<Rightarrow> 'cid option" where
  "calling_context (From_canister c _) = Some c"
| "calling_context _ = None"

fun message_queue :: "('b, 'p, 'uid, 'canid, 's, 'c, 'cid) message \<Rightarrow> 'canid queue option" where
  "message_queue (Call_message _ _ _ _ _ _ q) = Some q"
| "message_queue (Func_message _ _ _ q) = Some q"
| "message_queue _ = None"

(* Type conversion functions *)

fun simple_status :: "('b, 'p, 'uid, 'canid, 's, 'c, 'cid) can_status \<Rightarrow> status" where
  "simple_status can_status.Running = status.Running"
| "simple_status (can_status.Stopping _) = status.Stopping"
| "simple_status can_status.Stopped = status.Stopped"

(* Effective canister IDs *)

definition is_effective_canister_id :: "('b, 'p, 'uid, 'canid, 's) request \<Rightarrow> 'p \<Rightarrow> bool" where
  "is_effective_canister_id r p = (if request.canister_id r = ic_principal then
      (case candid_parse_cid (request.arg r) of Some cid \<Rightarrow> principal_of_canid cid = p
      | _ \<Rightarrow> request.method_name r = encode_string ''provisional_create_canister_with_cycles'')
    else principal_of_canid (request.canister_id r) = p)"

lemma is_effective_canister_id_code[code_unfold]:
  "(\<exists>p. is_effective_canister_id r p) = (if request.canister_id r = ic_principal then
      (case candid_parse_cid (request.arg r) of Some cid \<Rightarrow> True
      | _ \<Rightarrow> request.method_name r = encode_string ''provisional_create_canister_with_cycles'')
    else True)"
  by (auto simp: is_effective_canister_id_def split: option.splits)



(* System transition: API Request submission [DONE] *)

definition request_submission_pre :: "('b, 'p, 'uid, 'canid, 's, 'pk, 'sig, 'sd) envelope \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> bool" where
  "request_submission_pre E S = (case content E of Inl req \<Rightarrow>
    principal_of_canid (request.canister_id req) \<in> verify_envelope E (principal_of_uid (request.sender req)) (system_time S) \<and>
    req \<notin> list_map_dom (requests S) \<and>
    system_time S \<le> request.ingress_expiry req \<and>
    (\<exists>ECID. is_effective_canister_id req ECID) \<and>
    (
      (
        request.canister_id req = ic_principal \<and>
        (case candid_parse_cid (request.arg req) of Some cid \<Rightarrow>
          (case list_map_get (controllers S) cid of Some ctrls \<Rightarrow>
            principal_of_uid (request.sender req) \<in> ctrls \<and>
            request.method_name req \<in> {encode_string ''install_code'', encode_string ''update_settings'',
              encode_string ''start_canister'', encode_string ''stop_canister'',
              encode_string ''canister_status'', encode_string ''delete_canister'',
              encode_string ''provisional_create_canister_with_cycles'', encode_string ''provisional_top_up_canister''}
          | _ \<Rightarrow> False)
        | _ \<Rightarrow> False)
      )
    \<or>
      (
        request.canister_id req \<noteq> ic_principal \<and>
        (case (list_map_get (canisters S) (request.canister_id req), list_map_get (time S) (request.canister_id req), list_map_get (balances S) (request.canister_id req), list_map_get (canister_status S) (request.canister_id req)) of
          (Some (Some can), Some t, Some bal, Some can_status) \<Rightarrow>
          let env = \<lparr>env_time = t, balance = bal, freezing_limit = ic_freezing_limit S (request.canister_id req), certificate = None, status = simple_status can_status\<rparr> in
          (case canister_module_inspect_message (module can) (request.method_name req, wasm_state can, request.arg req, principal_of_uid (request.sender req), env) of Inr ret \<Rightarrow>
            cycles_return.return ret = Accept \<and> cycles_return.cycles_used ret \<le> bal
          | _ \<Rightarrow> False)
        | _ \<Rightarrow> False)
      )
    )
  | _ \<Rightarrow> False)"

definition request_submission_post :: "('b, 'p, 'uid, 'canid, 's, 'pk, 'sig, 'sd) envelope \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic" where
  "request_submission_post E S = (
    let req = projl (content E);
    cid = request.canister_id req;
    balances = (if request.canister_id req \<noteq> ic_principal then
      (case (list_map_get (canisters S) (request.canister_id req), list_map_get (time S) (request.canister_id req), list_map_get (balances S) (request.canister_id req), list_map_get (canister_status S) (request.canister_id req)) of
        (Some (Some can), Some t, Some bal, Some can_status) \<Rightarrow>
        let env = \<lparr>env_time = t, balance = bal, freezing_limit = ic_freezing_limit S (request.canister_id req), certificate = None, status = simple_status can_status\<rparr> in
        (case canister_module_inspect_message (module can) (request.method_name req, wasm_state can, request.arg req, principal_of_uid (request.sender req), env) of Inr ret \<Rightarrow>
          list_map_set (balances S) cid (bal - cycles_return.cycles_used ret)))
      else balances S) in
    S\<lparr>requests := list_map_set (requests S) req Received, balances := balances\<rparr>)"

definition request_submission_burned_cycles :: "('b, 'p, 'uid, 'canid, 's, 'pk, 'sig, 'sd) envelope \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> nat" where
  "request_submission_burned_cycles E S = (
    let req = projl (content E);
    cid = request.canister_id req in
    (if request.canister_id req \<noteq> ic_principal then
      (case (list_map_get (canisters S) (request.canister_id req), list_map_get (time S) (request.canister_id req), list_map_get (balances S) (request.canister_id req), list_map_get (canister_status S) (request.canister_id req)) of
        (Some (Some can), Some t, Some bal, Some can_status) \<Rightarrow>
        let env = \<lparr>env_time = t, balance = bal, freezing_limit = ic_freezing_limit S (request.canister_id req), certificate = None, status = simple_status can_status\<rparr> in
        (case canister_module_inspect_message (module can) (request.method_name req, wasm_state can, request.arg req, principal_of_uid (request.sender req), env) of Inr ret \<Rightarrow>
          cycles_return.cycles_used ret))
      else 0))"

lemma request_submission_cycles_inv:
  assumes "request_submission_pre E S"
  shows "total_cycles S = total_cycles (request_submission_post E S) + request_submission_burned_cycles E S"
proof -
  obtain req where req_def: "content E = Inl req"
    using assms
    by (auto simp: request_submission_pre_def split: sum.splits)
  {
    assume "request.canister_id req \<noteq> ic_principal"
    then have "(case (list_map_get (canisters S) (request.canister_id req), list_map_get (time S) (request.canister_id req), list_map_get (balances S) (request.canister_id req), list_map_get (canister_status S) (request.canister_id req)) of
      (Some (Some can), Some t, Some bal, Some can_status) \<Rightarrow>
      let env = \<lparr>env_time = t, balance = bal, freezing_limit = ic_freezing_limit S (request.canister_id req), certificate = None, status = simple_status can_status\<rparr> in
      (case canister_module_inspect_message (module can) (request.method_name req, wasm_state can, request.arg req, principal_of_uid (request.sender req), env) of Inr ret \<Rightarrow>
        cycles_return.return ret = Accept \<and> cycles_return.cycles_used ret \<le> bal
      | _ \<Rightarrow> False)
    | _ \<Rightarrow> False)"
      using assms
      by (auto simp: request_submission_pre_def req_def split: option.splits sum.splits prod.splits)
    then have ?thesis
      using list_map_sum_in_ge[where ?f="balances S" and ?g=id and ?x="request.canister_id req"]
      by (auto simp: request_submission_pre_def request_submission_post_def request_submission_burned_cycles_def total_cycles_def req_def list_map_sum_in[where ?f="balances S"]
          split: option.splits sum.splits)
  }
  then show ?thesis
    by (auto simp: request_submission_pre_def request_submission_post_def request_submission_burned_cycles_def total_cycles_def req_def)
qed



(* System transition: Request rejection [DONE] *)

definition request_rejection_pre :: "('b, 'p, 'uid, 'canid, 's, 'pk, 'sig, 'sd) envelope \<Rightarrow> ('b, 'p, 'uid, 'canid, 's) request \<Rightarrow> reject_code \<Rightarrow> 's \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> bool" where
  "request_rejection_pre E req code msg S = (list_map_get (requests S) req = Some Received \<and> (code = SYS_FATAL \<or> code = SYS_TRANSIENT))"

definition request_rejection_post :: "('b, 'p, 'uid, 'canid, 's, 'pk, 'sig, 'sd) envelope \<Rightarrow> ('b, 'p, 'uid, 'canid, 's) request \<Rightarrow> reject_code \<Rightarrow> 's \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic" where
  "request_rejection_post E req code msg S = S\<lparr>requests := list_map_set (requests S) req (Rejected code msg)\<rparr>"

lemma request_rejection_cycles_inv:
  assumes "request_rejection_pre E req code msg S"
  shows "total_cycles S = total_cycles (request_rejection_post E req code msg S)"
  by (auto simp: request_rejection_pre_def request_rejection_post_def total_cycles_def)



(* System transition: Initiating canister calls [DONE] *)

definition initiate_canister_call_pre :: "('b, 'p, 'uid, 'canid, 's) request \<Rightarrow>
  ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> bool" where
  "initiate_canister_call_pre req S = (list_map_get (requests S) req = Some Received \<and>
    system_time S \<le> request.ingress_expiry req \<and>
    request.canister_id req \<in> list_map_dom (canisters S))"

definition initiate_canister_call_post :: "('b, 'p, 'uid, 'canid, 's) request \<Rightarrow>
  ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow>
  ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic" where
  "initiate_canister_call_post req S =
    S\<lparr>requests := list_map_set (requests S) req Processing, messages :=
      Call_message (From_user req) (principal_of_uid (request.sender req)) (request.canister_id req) (request.method_name req)
      (request.arg req) 0 Unordered # messages S\<rparr>"

lemma initiate_canister_call_cycles_inv:
  assumes "initiate_canister_call_pre R S"
  shows "total_cycles S = total_cycles (initiate_canister_call_post R S)"
  by (auto simp: initiate_canister_call_pre_def initiate_canister_call_post_def total_cycles_def)



(* System transition: Calls to stopped/stopping/frozen canisters are rejected [DONE] *)

definition call_reject_pre :: "nat \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> bool" where
  "call_reject_pre n S = (n < length (messages S) \<and> (case messages S ! n of
    Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
      (q = Unordered \<or> (\<forall>j < n. message_queue (messages S ! j) \<noteq> Some q)) \<and>
      (case list_map_get (canister_status S) cee of Some Stopped \<Rightarrow> True
      | Some (Stopping l) \<Rightarrow> True
      | _ \<Rightarrow> (case list_map_get (balances S) cee of Some bal \<Rightarrow> bal < ic_freezing_limit S cee | _ \<Rightarrow> False))
    | _ \<Rightarrow> False))"

definition call_reject_post :: "nat \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic" where
  "call_reject_post n S = (case messages S ! n of Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    S\<lparr>messages := take n (messages S) @ drop (Suc n) (messages S) @ [Response_message orig (response.Reject CANISTER_ERROR (encode_string ''canister not running'')) trans_cycles]\<rparr>)"

lemma call_reject_cycles_inv:
  assumes "call_reject_pre n S"
  shows "total_cycles S = total_cycles (call_reject_post n S)"
proof -
  obtain orig cer cee mn a trans_cycles q where msg: "messages S ! n = Call_message orig cer cee mn a trans_cycles q"
    using assms
    by (auto simp: call_reject_pre_def split: message.splits)
  define older where "older = take n (messages S)"
  define younger where "younger = drop (Suc n) (messages S)"
  have msgs: "messages S = older @ Call_message orig cer cee mn a trans_cycles q # younger" "(older @ w # younger) ! n = w"
    "take n older = older" "take (n - length older) ws = []" "drop (Suc n) older = []"
    "drop (Suc n - length older) (w # ws) = ws" for w ws
    using id_take_nth_drop[of n "messages S"] assms
    by (auto simp: call_reject_pre_def msg younger_def older_def nth_append)
  show ?thesis
    using assms
    by (auto simp: call_reject_pre_def call_reject_post_def total_cycles_def Let_def msgs split: message.splits option.splits)
qed



(* System transition: Call context creation: Public entry points [DONE] *)

definition call_context_create_pre :: "nat \<Rightarrow> 'cid
  \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> bool" where
  "call_context_create_pre n ctxt_id S = (n < length (messages S) \<and> (case messages S ! n of
    Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
      (case list_map_get (canisters S) cee of Some (Some can) \<Rightarrow> True | _ \<Rightarrow> False) \<and>
      list_map_get (canister_status S) cee = Some Running \<and>
      (case list_map_get (balances S) cee of Some bal \<Rightarrow> bal \<ge> ic_freezing_limit S cee + MAX_CYCLES_PER_MESSAGE | None \<Rightarrow> False) \<and>
      ctxt_id \<notin> list_map_dom (call_contexts S)
    | _ \<Rightarrow> False))"

lift_definition create_call_ctxt :: "'canid \<Rightarrow> ('b, 'p, 'uid, 'canid, 's, 'c, 'cid) call_origin \<Rightarrow> nat \<Rightarrow>
  ('p, 'uid, 'canid, 'b, 's, 'c, 'cid) call_ctxt" is
  "\<lambda>cee orig trans_cycles. \<lparr>canister = cee, origin = orig, needs_to_respond = True, deleted = False, available_cycles = trans_cycles\<rparr>"
  by auto

lemma create_call_ctxt_carried_cycles[simp]: "call_ctxt_carried_cycles (create_call_ctxt cee orig trans_cycles) = carried_cycles orig + trans_cycles"
  by transfer auto

definition call_context_create_post :: "nat \<Rightarrow> 'cid \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic" where
  "call_context_create_post n ctxt_id S = (case messages S ! n of Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    case list_map_get (balances S) cee of Some bal \<Rightarrow>
    S\<lparr>messages := list_update (messages S) n (Func_message ctxt_id cee (Public_method mn cer a) q),
      call_contexts := list_map_set (call_contexts S) ctxt_id (create_call_ctxt cee orig trans_cycles),
      balances := list_map_set (balances S) cee (bal - MAX_CYCLES_PER_MESSAGE)\<rparr>)"

lemma call_context_create_cycles_inv:
  assumes "call_context_create_pre n ctxt_id S"
  shows "total_cycles S = total_cycles (call_context_create_post n ctxt_id S)"
proof -
  obtain orig cer cee mn a trans_cycles q where msg: "messages S ! n = Call_message orig cer cee mn a trans_cycles q"
    using assms
    by (auto simp: call_context_create_pre_def split: message.splits)
  define older where "older = take n (messages S)"
  define younger where "younger = drop (Suc n) (messages S)"
  have msgs: "messages S = older @ Call_message orig cer cee mn a trans_cycles q # younger" "(older @ m # younger) ! n = m"
    and msgs_upd: "(older @ Call_message orig cer cee mn a trans_cycles q # younger)[n := m] = older @ m # younger" for m
    using id_take_nth_drop[of n "messages S"] upd_conv_take_nth_drop[of n "messages S"] assms
    by (auto simp: call_context_create_pre_def msg older_def younger_def nth_append)
  show ?thesis
    using assms list_map_sum_in_ge[of "balances S" cee, where ?g=id]
    by (auto simp: call_context_create_pre_def call_context_create_post_def total_cycles_def
        list_map_sum_in[where ?g=id, simplified] list_map_sum_out msgs msgs_upd split: option.splits)
qed



(* System transition: Call context creation: Heartbeat [DONE] *)

definition call_context_heartbeat_pre :: "'canid \<Rightarrow> 'cid \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> bool" where
  "call_context_heartbeat_pre cee ctxt_id S = (
    (case list_map_get (canisters S) cee of Some (Some can) \<Rightarrow> True | _ \<Rightarrow> False) \<and>
    list_map_get (canister_status S) cee = Some Running \<and>
    (case list_map_get (balances S) cee of Some bal \<Rightarrow> bal \<ge> ic_freezing_limit S cee + MAX_CYCLES_PER_MESSAGE | _ \<Rightarrow> False) \<and>
    ctxt_id \<notin> list_map_dom (call_contexts S))"

lift_definition create_call_ctxt_heartbeat :: "'canid \<Rightarrow> ('p, 'uid, 'canid, 'b, 's, 'c, 'cid) call_ctxt" is
  "\<lambda>cee. \<lparr>canister = cee, origin = From_heartbeat, needs_to_respond = False, deleted = False, available_cycles = 0\<rparr>"
  by auto

lemma create_call_ctxt_heartbeat_carried_cycles[simp]: "call_ctxt_carried_cycles (create_call_ctxt_heartbeat cee) = 0"
  by transfer auto

definition call_context_heartbeat_post :: "'canid \<Rightarrow> 'cid \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic" where
  "call_context_heartbeat_post cee ctxt_id S =
  (case list_map_get (balances S) cee of Some bal \<Rightarrow>
    S\<lparr>messages := Func_message ctxt_id cee Heartbeat (Queue System cee) # messages S,
    call_contexts := list_map_set (call_contexts S) ctxt_id (create_call_ctxt_heartbeat cee),
    balances := list_map_set (balances S) cee (bal - MAX_CYCLES_PER_MESSAGE)\<rparr>)"

lemma call_context_heartbeat_cycles_inv:
  assumes "call_context_heartbeat_pre cee ctxt_id S"
  shows "total_cycles S = total_cycles (call_context_heartbeat_post cee ctxt_id S)"
  using assms list_map_sum_in_ge[of "balances S" cee, where ?g=id, simplified]
  by (auto simp: call_context_heartbeat_pre_def call_context_heartbeat_post_def total_cycles_def
      list_map_sum_in[where ?g=id, simplified] list_map_sum_out split: option.splits)



(* System transition: Message execution [DONE] *)

fun query_as_update :: "(('b arg \<times> 'p \<times> 'b env) \<Rightarrow> ('w, 'b, 's) query_func) \<times> 'b arg \<times> 'p \<times> 'b env \<Rightarrow> ('w, 'p, 'canid, 's, 'b, 'c) update_func" where
  "query_as_update (f, a, e) = (\<lambda>w. case f (a, e) w of Inl t \<Rightarrow> Inl t |
    Inr res \<Rightarrow> Inr \<lparr>update_return.new_state = w, update_return.new_calls = [], update_return.new_certified_data = None,
      update_return.response = Some (query_return.response res), update_return.cycles_accepted = 0, update_return.cycles_used = query_return.cycles_used res\<rparr>)"

fun heartbeat_as_update :: "('b env \<Rightarrow> 'w heartbeat_func) \<times> 'b env \<Rightarrow> ('w, 'p, 'canid, 's, 'b, 'c) update_func" where
  "heartbeat_as_update (f, e) = (\<lambda>w. case f e w of Inl t \<Rightarrow> Inl t |
    Inr res \<Rightarrow> Inr \<lparr>update_return.new_state = heartbeat_return.new_state res, update_return.new_calls = [], update_return.new_certified_data = None,
      update_return.response = None, update_return.cycles_accepted = 0, update_return.cycles_used = heartbeat_return.cycles_used res\<rparr>)"

fun exec_function :: "('s, 'p, 'b, 'c) entry_point \<Rightarrow> 'b env \<Rightarrow> nat \<Rightarrow> ('p, 'canid, 'b, 'w, 'sm, 'c, 's) canister_module \<Rightarrow> ('w, 'p, 'canid, 's, 'b, 'c) update_func" where
  "exec_function (entry_point.Public_method mn c a) e bal m = (
    case dispatch_method mn m of Some (Inl upd) \<Rightarrow> upd (a, c, e, bal)
    | Some (Inr query) \<Rightarrow> query_as_update (query, a, c, e) | None \<Rightarrow>
    undefined)"
| "exec_function (entry_point.Callback cb resp ref_cycles) e bal m =
    canister_module_callbacks m (cb, resp, ref_cycles, e, bal)"
| "exec_function (entry_point.Heartbeat) e bal m = heartbeat_as_update ((canister_module_heartbeat m), e)"

definition message_execution_pre :: "nat \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> bool" where
  "message_execution_pre n S =
    (n < length (messages S) \<and> (case messages S ! n of Func_message ctxt_id recv ep q \<Rightarrow>
    (q = Unordered \<or> (\<forall>j < n. message_queue (messages S ! j) \<noteq> Some q)) \<and>
    (case (list_map_get (canisters S) recv, list_map_get (balances S) recv, list_map_get (canister_status S) recv,
      list_map_get (time S) recv, list_map_get (call_contexts S) ctxt_id) of
      (Some (Some can), Some bal, Some can_status, Some t, Some ctxt) \<Rightarrow> True | _ \<Rightarrow> False)
    | _ \<Rightarrow> False))"

definition message_execution_post :: "nat \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic" where
  "message_execution_post n S = (case messages S ! n of Func_message ctxt_id recv ep q \<Rightarrow>
    (case (list_map_get (canisters S) recv, list_map_get (balances S) recv, list_map_get (canister_status S) recv,
      list_map_get (time S) recv, list_map_get (call_contexts S) ctxt_id) of
      (Some (Some can), Some bal, Some can_status, Some t, Some ctxt) \<Rightarrow> (
        let Mod = module can;
        Is_response = (case ep of Callback _ _ _ \<Rightarrow> True | _ \<Rightarrow> False);
        Env = \<lparr>env_time = t, balance = bal, freezing_limit = ic_freezing_limit S recv, certificate = None, status = simple_status can_status\<rparr>;
        Available = call_ctxt_available_cycles ctxt;
        F = exec_function ep Env Available Mod;
        R = F (wasm_state can);
        cyc_used = (case R of Inr res \<Rightarrow> update_return.cycles_used res | Inl trap \<Rightarrow> trap_return.cycles_used trap);
        (cycles_accepted_res, new_calls_res) = (case R of Inr res \<Rightarrow> (update_return.cycles_accepted res, update_return.new_calls res));
        New_balance = bal + cycles_accepted_res + (if Is_response then MAX_CYCLES_PER_RESPONSE else MAX_CYCLES_PER_MESSAGE)
          - (cyc_used + sum_list (map (\<lambda>x. MAX_CYCLES_PER_RESPONSE + transferred_cycles x) new_calls_res));
        no_response = (case R of Inr result \<Rightarrow> update_return.response result = None) in
        if \<not>isl R \<and> cyc_used \<le> (if Is_response then MAX_CYCLES_PER_RESPONSE else MAX_CYCLES_PER_MESSAGE) \<and>
          cycles_accepted_res \<le> Available \<and>
          cyc_used + sum_list (map (\<lambda>x. MAX_CYCLES_PER_RESPONSE + transferred_cycles x) new_calls_res) \<le>
            bal + cycles_accepted_res + (if Is_response then MAX_CYCLES_PER_RESPONSE else MAX_CYCLES_PER_MESSAGE) \<and>
          New_balance \<ge> (if Is_response then 0 else ic_freezing_limit S recv) \<and>
          (no_response \<or> call_ctxt_needs_to_respond ctxt) then
          (let result = projr R;
            new_call_to_message = (\<lambda>call. Call_message (From_canister ctxt_id (callback call)) (principal_of_canid recv)
              (method_call.callee call) (method_call.method_name call) (method_call.arg call) (method_call.transferred_cycles call) (Queue (Canister recv) (method_call.callee call)));
            response_messages = (case update_return.response result of None \<Rightarrow> []
              | Some resp \<Rightarrow> [Response_message (call_ctxt_origin ctxt) resp (Available - cycles_accepted_res)]);
            messages = take n (messages S) @ drop (Suc n) (messages S) @ map new_call_to_message new_calls_res @ response_messages;
            new_ctxt = (case update_return.response result of
              None \<Rightarrow> call_ctxt_deduct_cycles cycles_accepted_res ctxt
            | Some _ \<Rightarrow> call_ctxt_respond ctxt);
            certified_data = (case new_certified_data result of None \<Rightarrow> certified_data S
              | Some cd \<Rightarrow> list_map_set (certified_data S) recv cd)
            in S\<lparr>canisters := list_map_set (canisters S) recv (Some (can\<lparr>wasm_state := update_return.new_state result\<rparr>)),
              messages := messages, call_contexts := list_map_set (call_contexts S) ctxt_id new_ctxt,
              balances := list_map_set (balances S) recv New_balance, certified_data := certified_data\<rparr>)
        else S\<lparr>messages := take n (messages S) @ drop (Suc n) (messages S),
          balances := list_map_set (balances S) recv ((bal + (if Is_response then MAX_CYCLES_PER_RESPONSE else MAX_CYCLES_PER_MESSAGE))
            - min cyc_used (if Is_response then MAX_CYCLES_PER_RESPONSE else MAX_CYCLES_PER_MESSAGE))\<rparr>))
    | _ \<Rightarrow> undefined)"

definition message_execution_burned_cycles :: "nat \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> nat" where
  "message_execution_burned_cycles n S = (case messages S ! n of Func_message ctxt_id recv ep q \<Rightarrow>
    (case (list_map_get (canisters S) recv, list_map_get (balances S) recv, list_map_get (canister_status S) recv,
      list_map_get (time S) recv, list_map_get (call_contexts S) ctxt_id) of
      (Some (Some can), Some bal, Some can_status, Some t, Some ctxt) \<Rightarrow> (
        let Mod = module can;
        Is_response = (case ep of Callback _ _ _ \<Rightarrow> True | _ \<Rightarrow> False);
        Env = \<lparr>env_time = t, balance = bal, freezing_limit = ic_freezing_limit S recv, certificate = None, status = simple_status can_status\<rparr>;
        Available = call_ctxt_available_cycles ctxt;
        F = exec_function ep Env Available Mod;
        R = F (wasm_state can);
        cyc_used = (case R of Inr res \<Rightarrow> update_return.cycles_used res | Inl trap \<Rightarrow> trap_return.cycles_used trap) in
        min cyc_used (if Is_response then MAX_CYCLES_PER_RESPONSE else MAX_CYCLES_PER_MESSAGE)
      )))"

lemma message_execution_cycles_monotonic:
  assumes pre: "message_execution_pre n S"
  shows "total_cycles S = total_cycles (message_execution_post n S) + message_execution_burned_cycles n S"
proof -
  obtain ctxt_id recv ep q can bal can_status t ctxt where msg: "messages S ! n = Func_message ctxt_id recv ep q"
    and prod: "list_map_get (canisters S) recv = Some (Some can)"
    "list_map_get (balances S) recv = Some bal"
    "list_map_get (canister_status S) recv = Some can_status"
    "list_map_get (time S) recv = Some t"
    "list_map_get (call_contexts S) ctxt_id = Some ctxt"
    using pre
    by (auto simp: message_execution_pre_def split: message.splits option.splits)
  define Mod where "Mod = can_state_rec.module can"
  define Is_response where "Is_response = (case ep of Callback _ _ _ \<Rightarrow> True | _ \<Rightarrow> False)"
  define Env :: "'b env" where "Env = \<lparr>env_time = t, balance = bal, freezing_limit = ic_freezing_limit S recv, certificate = None, status = simple_status can_status\<rparr>"
  define Available where "Available = call_ctxt_available_cycles ctxt"
  define F where "F = exec_function ep Env Available Mod"
  define R where "R = F (wasm_state can)"
  define cyc_used where "cyc_used = (case R of Inr res \<Rightarrow> update_return.cycles_used res | Inl trap \<Rightarrow> trap_return.cycles_used trap)"
  obtain cycles_accepted_res new_calls_res where res: "(cycles_accepted_res, new_calls_res) = (case R of Inr res \<Rightarrow> (update_return.cycles_accepted res, new_calls res))"
    by (cases "(case R of Inr res \<Rightarrow> (update_return.cycles_accepted res, new_calls res))") auto
  define New_balance where "New_balance = bal + cycles_accepted_res + (if Is_response then MAX_CYCLES_PER_RESPONSE else MAX_CYCLES_PER_MESSAGE)
    - (cyc_used + sum_list (map (\<lambda>x. MAX_CYCLES_PER_RESPONSE + transferred_cycles x) new_calls_res))"
  define no_response where "no_response = (case R of Inr result \<Rightarrow> update_return.response result = None)"
  define older where "older = take n (messages S)"
  define younger where "younger = drop (Suc n) (messages S)"
  have msgs: "messages S = older @ Func_message ctxt_id recv ep q # younger"
    "take n older = older" "drop (Suc n) older = []"
    "take (n - length older) ws = []" "drop (Suc n - length older) (w # ws) = ws"
    for w and ws :: "('b, 'p, 'uid, 'canid, 's, 'c, 'cid) message list"
    using id_take_nth_drop[of n "messages S"] pre
    by (auto simp: message_execution_pre_def msg older_def younger_def)
  note lm = list_map_sum_in[OF prod(2), where ?g=id, simplified] list_map_sum_in_ge[OF prod(2), where ?g=id, simplified]
    list_map_sum_in[OF prod(5), where ?g=call_ctxt_carried_cycles] list_map_sum_in_ge[OF prod(5), where ?g=call_ctxt_carried_cycles]
  define S'' where "S'' = S\<lparr>messages := take n (messages S) @ drop (Suc n) (messages S),
    balances := list_map_set (balances S) recv ((bal + (if Is_response then MAX_CYCLES_PER_RESPONSE else MAX_CYCLES_PER_MESSAGE)) - min cyc_used (if Is_response then MAX_CYCLES_PER_RESPONSE else MAX_CYCLES_PER_MESSAGE))\<rparr>"
  define cond where "cond = (\<not>isl R \<and> cyc_used \<le> (if Is_response then MAX_CYCLES_PER_RESPONSE else MAX_CYCLES_PER_MESSAGE) \<and>
    cycles_accepted_res \<le> Available \<and>
    cyc_used + sum_list (map (\<lambda>x. MAX_CYCLES_PER_RESPONSE + transferred_cycles x) new_calls_res) \<le>
      bal + cycles_accepted_res + (if Is_response then MAX_CYCLES_PER_RESPONSE else MAX_CYCLES_PER_MESSAGE) \<and>
    New_balance \<ge> (if Is_response then 0 else ic_freezing_limit S recv) \<and>
    (no_response \<or> call_ctxt_needs_to_respond ctxt))"
  have reserved: "(if Is_response then MAX_CYCLES_PER_RESPONSE else MAX_CYCLES_PER_MESSAGE) = cycles_reserved ep"
    by (auto simp: Is_response_def split: entry_point.splits)
  show ?thesis
  proof (cases cond)
    case False
    have "message_execution_post n S = S''"
      "message_execution_burned_cycles n S = min cyc_used (if Is_response then MAX_CYCLES_PER_RESPONSE else MAX_CYCLES_PER_MESSAGE)"
      using False
      by (simp_all add: message_execution_post_def message_execution_burned_cycles_def Let_def msg prod
          Mod_def[symmetric] Is_response_def[symmetric] Env_def[symmetric] Available_def[symmetric] F_def[symmetric] R_def[symmetric] cyc_used_def[symmetric] res[symmetric]
          New_balance_def[symmetric] no_response_def[symmetric] S''_def[symmetric] cond_def[symmetric] del: min_less_iff_conj split del: if_split)
    then show ?thesis
      using lm(2)
      by (auto simp: total_cycles_def S''_def msgs lm(1) reserved)
  next
    case True
    define result where "result = projr R"
    have R_Inr: "R = Inr result"
      using True
      by (auto simp: cond_def result_def split: option.splits)
    define response_messages where "response_messages = (case update_return.response result of None \<Rightarrow> []
      | Some resp \<Rightarrow> [Response_message (call_ctxt_origin ctxt) resp (Available - cycles_accepted_res)])"
    define new_call_to_message :: "(?'p, 'canid, 's, 'b, 'c) method_call \<Rightarrow> ('b, 'p, 'uid, 'canid, 's, 'c, 'cid) message" where
      "new_call_to_message = (\<lambda>call. Call_message (From_canister ctxt_id (callback call)) (principal_of_canid recv)
        (callee call) (method_call.method_name call) (method_call.arg call) (transferred_cycles call) (Queue (Canister recv) (callee call)))"
    define messages where "messages = take n (ic.messages S) @ drop (Suc n) (ic.messages S) @ map new_call_to_message new_calls_res @ response_messages"
    define new_ctxt where "new_ctxt = (case update_return.response result of
        None \<Rightarrow> call_ctxt_deduct_cycles cycles_accepted_res ctxt
      | Some _ \<Rightarrow> call_ctxt_respond ctxt)"
    define certified_data where "certified_data = (case new_certified_data result of None \<Rightarrow> ic.certified_data S
      | Some cd \<Rightarrow> list_map_set (ic.certified_data S) recv cd)"
    define S' where "S' = S\<lparr>canisters := list_map_set (canisters S) recv (Some (can\<lparr>wasm_state := update_return.new_state result\<rparr>)),
      messages := messages, call_contexts := list_map_set (call_contexts S) ctxt_id new_ctxt,
      balances := list_map_set (balances S) recv New_balance, certified_data := certified_data\<rparr>"
    have cycles_accepted_res_def: "cycles_accepted_res = update_return.cycles_accepted result"
      and new_calls_res_def: "new_calls_res = new_calls result"
      using res
      by (auto simp: R_Inr)
    have no_response: "no_response = (update_return.response result = None)"
      by (auto simp: no_response_def R_Inr)
    have msg_exec: "message_execution_post n S = S'"
      and lost: "message_execution_burned_cycles n S = min cyc_used (if Is_response then MAX_CYCLES_PER_RESPONSE else MAX_CYCLES_PER_MESSAGE)"
      using True
      by (simp_all add: message_execution_post_def message_execution_burned_cycles_def Let_def msg prod
          Mod_def[symmetric] Is_response_def[symmetric] Env_def[symmetric] Available_def[symmetric] F_def[symmetric] R_def[symmetric] cyc_used_def[symmetric] res[symmetric]
          New_balance_def[symmetric] no_response_def[symmetric] S''_def[symmetric] cond_def[symmetric]
          messages_def[symmetric] new_ctxt_def[symmetric] certified_data_def[symmetric] S'_def[symmetric]
          result_def[symmetric] response_messages_def[symmetric] new_call_to_message_def[symmetric]
          del: min_less_iff_conj split del: if_split)
    have "message_cycles \<circ> new_call_to_message = (\<lambda>c. MAX_CYCLES_PER_RESPONSE + transferred_cycles c)" for c :: "(?'p, 'canid, 's, 'b, 'c) method_call"
      by (auto simp: new_call_to_message_def)
    then have A1: "sum_list (map (message_cycles \<circ> new_call_to_message) new_calls_res) = (\<Sum>x\<leftarrow>new_calls_res. MAX_CYCLES_PER_RESPONSE + transferred_cycles x)"
      by auto
    have A2: "sum_list (map local.message_cycles response_messages) = (case update_return.response result of None \<Rightarrow> 0
      | _ \<Rightarrow> carried_cycles (call_ctxt_origin ctxt) + (call_ctxt_available_cycles ctxt - update_return.cycles_accepted result))"
      by (auto simp: response_messages_def Available_def cycles_accepted_res_def split: option.splits)
    have A3: "call_ctxt_carried_cycles new_ctxt = (case update_return.response result of Some _ \<Rightarrow> 0
      | _ \<Rightarrow> if call_ctxt_needs_to_respond ctxt then carried_cycles (call_ctxt_origin ctxt) + (call_ctxt_available_cycles ctxt - update_return.cycles_accepted result) else 0)"
      by (auto simp: new_ctxt_def Available_def cycles_accepted_res_def call_ctxt_carried_cycles split: option.splits)
    have A4: "call_ctxt_carried_cycles ctxt = (if call_ctxt_needs_to_respond ctxt then carried_cycles (call_ctxt_origin ctxt) + call_ctxt_available_cycles ctxt else 0)"
      using call_ctxt_carried_cycles
      by auto
    have reserve: "cycles_reserved ep = (if Is_response then MAX_CYCLES_PER_RESPONSE else MAX_CYCLES_PER_MESSAGE)"
      by (auto simp: Is_response_def split: entry_point.splits)
    have messages_msgs: "messages = older @ younger @ map new_call_to_message new_calls_res @ response_messages"
      by (auto simp: messages_def older_def younger_def)
    show ?thesis
      using lm(2,4) True call_ctxt_not_needs_to_respond_available_cycles[of ctxt]
      by (auto simp: cond_def msg_exec S'_def total_cycles_def lm(1,3) msgs messages_msgs A1 A2 A3 A4 New_balance_def
          reserve cycles_accepted_res_def no_response_def R_Inr lost Available_def split: option.splits)
  qed
qed



(* System transition: Call context starvation [DONE] *)

definition call_context_starvation_pre :: "'cid \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> bool" where
  "call_context_starvation_pre ctxt_id S =
  (case list_map_get (call_contexts S) ctxt_id of Some call_context \<Rightarrow>
    call_ctxt_needs_to_respond call_context \<and>
    call_ctxt_origin call_context \<noteq> From_heartbeat \<and>
    (\<forall>msg \<in> set (messages S). case msg of
        Call_message orig _ _ _ _ _ _ \<Rightarrow> calling_context orig \<noteq> Some ctxt_id
      | Response_message orig _ _ \<Rightarrow> calling_context orig \<noteq> Some ctxt_id
      | _ \<Rightarrow> True) \<and>
    (\<forall>other_call_context \<in> list_map_range (call_contexts S).
      call_ctxt_needs_to_respond other_call_context \<longrightarrow>
      calling_context (call_ctxt_origin other_call_context) \<noteq> Some ctxt_id)
  | None \<Rightarrow> False)"

definition call_context_starvation_post :: "'cid \<Rightarrow>
  ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic" where
  "call_context_starvation_post ctxt_id S = (
    case list_map_get (call_contexts S) ctxt_id of Some call_context \<Rightarrow>
    let msg = Response_message (call_ctxt_origin call_context) (response.Reject CANISTER_ERROR (encode_string ''starvation'')) (call_ctxt_available_cycles call_context)
    in S\<lparr>call_contexts := list_map_set (call_contexts S) ctxt_id (call_ctxt_respond call_context),
        messages := messages S @ [msg]\<rparr>)"

lemma call_context_starvation_cycles_inv:
  assumes "call_context_starvation_pre ctxt_id S"
  shows "total_cycles S = total_cycles (call_context_starvation_post ctxt_id S)"
  using assms list_map_sum_in_ge[where ?f="call_contexts S" and ?x=ctxt_id and ?g=call_ctxt_carried_cycles]
  by (auto simp: call_context_starvation_pre_def call_context_starvation_post_def total_cycles_def
      call_ctxt_carried_cycles list_map_sum_in[where ?g=call_ctxt_carried_cycles] split: option.splits)



(* System transition: Call context removal [DONE] *)

definition call_context_removal_pre :: "'cid \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> bool" where
  "call_context_removal_pre ctxt_id S = (
    (case list_map_get (call_contexts S) ctxt_id of Some call_context \<Rightarrow>
      (\<not>call_ctxt_needs_to_respond call_context \<or>
        (call_ctxt_origin call_context = From_heartbeat \<and>
          (\<forall>msg \<in> set (messages S). case msg of
            Func_message other_ctxt_id _ _ _ \<Rightarrow> other_ctxt_id \<noteq> ctxt_id
          | _ \<Rightarrow> True))) \<and>
      (\<forall>msg \<in> set (messages S). case msg of
          Call_message ctxt _ _ _ _ _ _ \<Rightarrow> calling_context ctxt \<noteq> Some ctxt_id
        | Response_message ctxt _ _ \<Rightarrow> calling_context ctxt \<noteq> Some ctxt_id
        | _ \<Rightarrow> True) \<and>
      (\<forall>other_call_context \<in> list_map_range (call_contexts S).
        call_ctxt_needs_to_respond other_call_context \<longrightarrow>
        calling_context (call_ctxt_origin other_call_context) \<noteq> Some ctxt_id)
    | None \<Rightarrow> False))"

definition call_context_removal_post :: "'cid \<Rightarrow>
  ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic" where
  "call_context_removal_post ctxt_id S = S\<lparr>call_contexts := list_map_del (call_contexts S) ctxt_id\<rparr>"

definition call_context_removal_burned_cycles :: "'cid \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> nat" where
  "call_context_removal_burned_cycles ctxt_id S = call_ctxt_available_cycles (the (list_map_get (call_contexts S) ctxt_id))"

lemma call_context_removal_cycles_monotonic:
  assumes "call_context_removal_pre ctxt_id S"
  shows "total_cycles S = total_cycles (call_context_removal_post ctxt_id S) + call_context_removal_burned_cycles ctxt_id S"
  using assms call_ctxt_not_needs_to_respond_available_cycles
  by (auto simp: call_context_removal_pre_def call_context_removal_post_def call_context_removal_burned_cycles_def total_cycles_def call_ctxt_carried_cycles list_map_del_sum split: option.splits)



(* System transition: IC Management Canister: Canister creation [DONE] *)

definition ic_canister_creation_pre :: "nat \<Rightarrow> 'canid \<Rightarrow> nat \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> bool" where
  "ic_canister_creation_pre n cid t S = (n < length (messages S) \<and> (case messages S ! n of
    Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
      (q = Unordered \<or> (\<forall>j < n. message_queue (messages S ! j) \<noteq> Some q)) \<and>
      cee = ic_principal \<and>
      mn = encode_string ''create_canister'' \<and>
      is_system_assigned (principal_of_canid cid) \<and>
      cid \<notin> list_map_dom (canisters S) \<and>
      cid \<notin> list_map_dom (time S) \<and>
      cid \<notin> list_map_dom (controllers S) \<and>
      cid \<notin> list_map_dom (balances S) \<and>
      cid \<notin> list_map_dom (certified_data S) \<and>
      cid \<notin> list_map_dom (canister_status S)
    | _ \<Rightarrow> False))"

definition ic_canister_creation_post :: "nat \<Rightarrow> 'canid \<Rightarrow> nat \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic" where
  "ic_canister_creation_post n cid t S = (case messages S ! n of Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    let ctrls = (case candid_parse_controllers a of Some ctrls \<Rightarrow> ctrls | _ \<Rightarrow> {cer}) in
    S\<lparr>canisters := list_map_set (canisters S) cid None,
      time := list_map_set (time S) cid t,
      controllers := list_map_set (controllers S) cid ctrls,
      balances := list_map_set (balances S) cid trans_cycles,
      certified_data := list_map_set (certified_data S) cid empty_blob,
      messages := take n (messages S) @ drop (Suc n) (messages S) @ [Response_message orig (Reply (blob_of_candid
        (Candid_record (list_map_init [(encode_string ''canister_id'', Candid_blob (blob_of_canid cid))])))) 0],
      canister_status := list_map_set (canister_status S) cid Running\<rparr>)"

lemma ic_canister_creation_cycles_inv:
  assumes "ic_canister_creation_pre n cid t S"
  shows "total_cycles S = total_cycles (ic_canister_creation_post n cid t S)"
proof -
  obtain orig cer cee mn a trans_cycles q where msg: "messages S ! n = Call_message orig cer cee mn a trans_cycles q"
    using assms
    by (auto simp: ic_canister_creation_pre_def split: message.splits)
  define older where "older = take n (messages S)"
  define younger where "younger = drop (Suc n) (messages S)"
  have msgs: "messages S = older @ Call_message orig cer cee mn a trans_cycles q # younger" "(older @ w # younger) ! n = w"
    "take n older = older" "take (n - length older) ws = []" "drop (Suc n) older = []"
    "drop (Suc n - length older) (w # ws) = ws" for w ws
    using id_take_nth_drop[of n "messages S"] assms
    by (auto simp: ic_canister_creation_pre_def msg younger_def older_def nth_append)
  show ?thesis
    using assms
    by (auto simp: ic_canister_creation_pre_def ic_canister_creation_post_def total_cycles_def Let_def msgs
        list_map_sum_out[where ?g=id] list_map_sum_out[where ?g=status_cycles] split: message.splits option.splits)
qed



(* System transition: IC Management Canister: Changing settings [DONE] *)

definition ic_update_settings_pre :: "nat \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> bool" where
  "ic_update_settings_pre n S = (n < length (messages S) \<and> (case messages S ! n of
    Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
      (q = Unordered \<or> (\<forall>j < n. message_queue (messages S ! j) \<noteq> Some q)) \<and>
      cee = ic_principal \<and>
      mn = encode_string ''update_settings'' \<and>
      (case candid_parse_cid a of Some cid \<Rightarrow>
      (case list_map_get (controllers S) cid of Some ctrls \<Rightarrow> cer \<in> ctrls | _ \<Rightarrow> False) | _ \<Rightarrow> False)
    | _ \<Rightarrow> False))"

definition ic_update_settings_post :: "nat \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic" where
  "ic_update_settings_post n S = (case messages S ! n of Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    let cid = the (candid_parse_cid a);
    ctrls = (case candid_parse_controllers a of Some ctrls \<Rightarrow> list_map_set (controllers S) cid ctrls | _ \<Rightarrow> controllers S);
    freezing_thres = (case candid_nested_lookup a [encode_string '''settings'', encode_string ''freezing_threshold''] of Some (Candid_nat freeze) \<Rightarrow>
      list_map_set (freezing_threshold S) cid freeze | _ \<Rightarrow> freezing_threshold S) in
    S\<lparr>controllers := ctrls, freezing_threshold := freezing_thres, messages := take n (messages S) @ drop (Suc n) (messages S) @
        [Response_message orig (Reply (blob_of_candid Candid_empty)) trans_cycles]\<rparr>)"

lemma ic_update_settings_cycles_inv:
  assumes "ic_update_settings_pre n S"
  shows "total_cycles S = total_cycles (ic_update_settings_post n S)"
proof -
  obtain orig cer cee mn a trans_cycles q where msg: "messages S ! n = Call_message orig cer cee mn a trans_cycles q"
    using assms
    by (auto simp: ic_update_settings_pre_def split: message.splits)
  define older where "older = take n (messages S)"
  define younger where "younger = drop (Suc n) (messages S)"
  have msgs: "messages S = older @ Call_message orig cer cee mn a trans_cycles q # younger" "(older @ w # younger) ! n = w"
    "take n older = older" "take (n - length older) ws = []" "drop (Suc n) older = []"
    "drop (Suc n - length older) (w # ws) = ws" for w ws
    using id_take_nth_drop[of n "messages S"] assms
    by (auto simp: ic_update_settings_pre_def msg younger_def older_def nth_append)
  show ?thesis
    using assms
    by (auto simp: ic_update_settings_pre_def ic_update_settings_post_def total_cycles_def Let_def msgs split: message.splits option.splits)
qed



(* System transition: IC Management Canister: Canister status [DONE] *)

definition ic_canister_status_pre :: "nat \<Rightarrow> nat \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> bool" where
  "ic_canister_status_pre n m S = (n < length (messages S) \<and> (case messages S ! n of Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    (q = Unordered \<or> (\<forall>j < n. message_queue (messages S ! j) \<noteq> Some q)) \<and>
    cee = ic_principal \<and>
    mn = encode_string ''canister_status'' \<and>
    (case candid_parse_cid a of Some cid \<Rightarrow>
      cid \<in> list_map_dom (canister_status S) \<and>
      cid \<in> list_map_dom (canisters S) \<and>
      cid \<in> list_map_dom (balances S) \<and>
      cid \<in> list_map_dom (freezing_threshold S) \<and>
    (case list_map_get (controllers S) cid of Some ctrls \<Rightarrow> cer \<in> ctrls | _ \<Rightarrow> False) | _ \<Rightarrow> False)
  | _ \<Rightarrow> False))"

definition ic_canister_status_post :: "nat \<Rightarrow> nat \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic" where
  "ic_canister_status_post n m S = (case messages S ! n of Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    let cid = the (candid_parse_cid a);
    hash = (case the (list_map_get (canisters S) cid) of None \<Rightarrow> Candid_null
      | Some can \<Rightarrow> Candid_opt (Candid_blob (sha_256 (raw_module can)))) in
    S\<lparr>messages := take n (messages S) @ drop (Suc n) (messages S) @ [Response_message orig (Reply (blob_of_candid
      (Candid_record (list_map_init [(encode_string ''status'', candid_of_status (simple_status (the (list_map_get (canister_status S) cid)))),
        (encode_string ''module_hash'', hash),
        (encode_string ''controllers'', Candid_vec (map (Candid_blob \<circ> blob_of_principal) (sorted_list_of_set (the (list_map_get (controllers S) cid))))),
        (encode_string ''memory_size'', Candid_nat m),
        (encode_string ''cycles'', Candid_nat (the (list_map_get (balances S) cid))),
        (encode_string ''freezing_threshold'', Candid_nat (the (list_map_get (freezing_threshold S) cid))),
        (encode_string ''idle_cycles_burned_per_day'', Candid_nat (ic_idle_cycles_burned_per_day S cid))])))) trans_cycles]\<rparr>)"

lemma ic_canister_status_cycles_inv:
  assumes "ic_canister_status_pre n m S"
  shows "total_cycles S = total_cycles (ic_canister_status_post n m S)"
proof -
  obtain orig cer cee mn a trans_cycles q where msg: "messages S ! n = Call_message orig cer cee mn a trans_cycles q"
    using assms
    by (auto simp: ic_canister_status_pre_def split: message.splits)
  define older where "older = take n (messages S)"
  define younger where "younger = drop (Suc n) (messages S)"
  have msgs: "messages S = older @ Call_message orig cer cee mn a trans_cycles q # younger" "(older @ w # younger) ! n = w"
    "take n older = older" "take (n - length older) ws = []" "drop (Suc n) older = []"
    "drop (Suc n - length older) (w # ws) = ws" for w ws
    using id_take_nth_drop[of n "messages S"] assms
    by (auto simp: ic_canister_status_pre_def msg younger_def older_def nth_append)
  show ?thesis
    using assms
    by (auto simp: ic_canister_status_pre_def ic_canister_status_post_def total_cycles_def Let_def msgs split: message.splits option.splits)
qed



(* System transition: IC Management Canister: Code installation [DONE] *)

definition ic_code_installation_pre :: "nat \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> bool" where
  "ic_code_installation_pre n S = (n < length (messages S) \<and> (case messages S ! n of Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    (q = Unordered \<or> (\<forall>j < n. message_queue (messages S ! j) \<noteq> Some q)) \<and>
    cee = ic_principal \<and>
    mn = encode_string ''install_code'' \<and>
    (case candid_parse_cid a of Some cid \<Rightarrow>
    (case (candid_parse_text a [encode_string ''mode''], candid_parse_blob a [encode_string ''wasm_module''], candid_parse_blob a [encode_string ''arg'']) of
      (Some mode, Some w, Some a) \<Rightarrow>
    (case parse_wasm_mod w of Some m \<Rightarrow>
      parse_public_custom_sections w \<noteq> None \<and>
      parse_private_custom_sections w \<noteq> None \<and>
    (case (list_map_get (controllers S) cid, list_map_get (time S) cid, list_map_get (balances S) cid, list_map_get (canister_status S) cid) of
      (Some ctrls, Some t, Some bal, Some can_status) \<Rightarrow>
      let env = \<lparr>env_time = t, balance = bal, freezing_limit = ic_freezing_limit S cid, certificate = None, status = simple_status can_status\<rparr> in
      ((mode = encode_string ''install'' \<and> (case list_map_get (canisters S) cid of Some None \<Rightarrow> True | _ \<Rightarrow> False)) \<or> mode = encode_string ''reinstall'') \<and>
      cer \<in> ctrls \<and>
      (case canister_module_init m (cid, a, cer, env) of Inl _ \<Rightarrow> False
      | Inr ret \<Rightarrow> cycles_return.cycles_used ret \<le> bal) \<and>
      list_map_dom (canister_module_update_methods m) \<inter> list_map_dom (canister_module_query_methods m) = {}
    | _ \<Rightarrow> False) | _ \<Rightarrow> False) | _ \<Rightarrow> False) | _ \<Rightarrow> False)
  | _ \<Rightarrow> False))"

definition ic_code_installation_post :: "nat \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic" where
  "ic_code_installation_post n S = (case messages S ! n of Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    let cid = the (candid_parse_cid a) in
    (case candid_parse_cid a of Some cid \<Rightarrow>
    (case (candid_parse_text a [encode_string ''mode''], candid_parse_blob a [encode_string ''wasm_module''], candid_parse_blob a [encode_string ''arg'']) of
      (Some mode, Some w, Some a) \<Rightarrow>
    (case parse_wasm_mod w of Some m \<Rightarrow>
    (case (list_map_get (time S) cid, list_map_get (balances S) cid, list_map_get (canister_status S) cid) of
      (Some t, Some bal, Some can_status) \<Rightarrow>
      let env = \<lparr>env_time = t, balance = bal, freezing_limit = ic_freezing_limit S cid, certificate = None, status = simple_status can_status\<rparr>;
      (new_state, cyc_used) = (case canister_module_init m (cid, a, cer, env) of Inr ret \<Rightarrow> (cycles_return.return ret, cycles_return.cycles_used ret)) in
    S\<lparr>canisters := list_map_set (canisters S) cid (Some \<lparr>wasm_state = new_state, module = m, raw_module = w,
        public_custom_sections = the (parse_public_custom_sections w), private_custom_sections = the (parse_private_custom_sections w)\<rparr>),
      balances := list_map_set (balances S) cid (bal - cyc_used),
      messages := take n (messages S) @ drop (Suc n) (messages S) @ [Response_message orig (Reply (blob_of_candid Candid_empty)) trans_cycles]\<rparr>)))))"

definition ic_code_installation_burned_cycles :: "nat \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> nat" where
  "ic_code_installation_burned_cycles n S = (case messages S ! n of Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    let cid = the (candid_parse_cid a) in
    (case candid_parse_cid a of Some cid \<Rightarrow>
    (case (candid_parse_blob a [encode_string ''wasm_module''], candid_parse_blob a [encode_string ''arg'']) of
      (Some w, Some a) \<Rightarrow>
    (case parse_wasm_mod w of Some m \<Rightarrow>
    (case (list_map_get (time S) cid, list_map_get (balances S) cid, list_map_get (canister_status S) cid) of
      (Some t, Some bal, Some can_status) \<Rightarrow>
      let env = \<lparr>env_time = t, balance = bal, freezing_limit = ic_freezing_limit S cid, certificate = None, status = simple_status can_status\<rparr> in
      (case canister_module_init m (cid, a, cer, env) of Inr ret \<Rightarrow> cycles_return.cycles_used ret))))))"

lemma ic_code_installation_cycles_inv:
  assumes "ic_code_installation_pre n S"
  shows "total_cycles S = total_cycles (ic_code_installation_post n S) + ic_code_installation_burned_cycles n S"
proof -
  obtain orig cer cee mn a trans_cycles q where msg: "messages S ! n = Call_message orig cer cee mn a trans_cycles q"
    using assms
    by (auto simp: ic_code_installation_pre_def split: message.splits)
  define older where "older = take n (messages S)"
  define younger where "younger = drop (Suc n) (messages S)"
  have msgs: "messages S = older @ Call_message orig cer cee mn a trans_cycles q # younger" "(older @ w # younger) ! n = w"
    "take n older = older" "take (n - length older) ws = []" "drop (Suc n) older = []"
    "drop (Suc n - length older) (w # ws) = ws" for w ws
    using id_take_nth_drop[of n "messages S"] assms
    by (auto simp: ic_code_installation_pre_def msg younger_def older_def nth_append)
  show ?thesis
    using assms list_map_sum_in_ge[where ?f="balances S" and ?g=id and ?x="the (candid_parse_cid a)"]
    by (auto simp: ic_code_installation_pre_def ic_code_installation_post_def ic_code_installation_burned_cycles_def total_cycles_def Let_def msgs list_map_sum_in[where ?f="balances S"] split: message.splits option.splits sum.splits prod.splits)
qed



(* System transition: IC Management Canister: Code upgrade [DONE] *)

definition ic_code_upgrade_pre :: "nat \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> bool" where
  "ic_code_upgrade_pre n S = (n < length (messages S) \<and> (case messages S ! n of Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    (q = Unordered \<or> (\<forall>j < n. message_queue (messages S ! j) \<noteq> Some q)) \<and>
    cee = ic_principal \<and>
    mn = encode_string ''install_code'' \<and>
    (case candid_parse_cid a of Some cid \<Rightarrow>
    (case (candid_parse_text a [encode_string ''mode''], candid_parse_blob a [encode_string ''wasm_module''], candid_parse_blob a [encode_string ''arg'']) of
      (Some mode, Some w, Some a) \<Rightarrow>
    (case parse_wasm_mod w of Some m \<Rightarrow>
      parse_public_custom_sections w \<noteq> None \<and>
      parse_private_custom_sections w \<noteq> None \<and>
    (case (list_map_get (canisters S) cid, list_map_get (controllers S) cid, list_map_get (time S) cid, list_map_get (balances S) cid, list_map_get (canister_status S) cid) of
      (Some (Some can), Some ctrls, Some t, Some bal, Some can_status) \<Rightarrow>
      let env = \<lparr>env_time = t, balance = bal, freezing_limit = ic_freezing_limit S cid, certificate = None, status = simple_status can_status\<rparr> in
      mode = encode_string ''upgrade'' \<and>
      cer \<in> ctrls \<and>
      (case canister_module_pre_upgrade (module can) (wasm_state can, cer, env) of Inr pre_ret \<Rightarrow>
      (case canister_module_post_upgrade m (cid, cycles_return.return pre_ret, a, cer, env) of Inr post_ret \<Rightarrow>
        cycles_return.cycles_used pre_ret + cycles_return.cycles_used post_ret \<le> bal
      | _ \<Rightarrow> False) | _ \<Rightarrow> False) \<and>
      list_map_dom (canister_module_update_methods m) \<inter> list_map_dom (canister_module_query_methods m) = {}
    | _ \<Rightarrow> False) | _ \<Rightarrow> False) | _ \<Rightarrow> False) | _ \<Rightarrow> False)
  | _ \<Rightarrow> False))"

definition ic_code_upgrade_post :: "nat \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic" where
  "ic_code_upgrade_post n S = (case messages S ! n of Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    let cid = the (candid_parse_cid a) in
    (case candid_parse_cid a of Some cid \<Rightarrow>
    (case (candid_parse_text a [encode_string ''mode''], candid_parse_blob a [encode_string ''wasm_module''], candid_parse_blob a [encode_string ''arg'']) of
      (Some mode, Some w, Some a) \<Rightarrow>
    (case parse_wasm_mod w of Some m \<Rightarrow>
    (case (list_map_get (canisters S) cid, list_map_get (time S) cid, list_map_get (balances S) cid, list_map_get (canister_status S) cid) of
      (Some (Some can), Some t, Some bal, Some can_status) \<Rightarrow>
      let env = \<lparr>env_time = t, balance = bal, freezing_limit = ic_freezing_limit S cid, certificate = None, status = simple_status can_status\<rparr> in
      (case canister_module_pre_upgrade (module can) (wasm_state can, cer, env) of Inr pre_ret \<Rightarrow>
      (case canister_module_post_upgrade m (cid, cycles_return.return pre_ret, a, cer, env) of Inr post_ret \<Rightarrow>
    S\<lparr>canisters := list_map_set (canisters S) cid (Some \<lparr>wasm_state = cycles_return.return post_ret, module = m, raw_module = w,
        public_custom_sections = the (parse_public_custom_sections w), private_custom_sections = the (parse_private_custom_sections w)\<rparr>),
      balances := list_map_set (balances S) cid (bal - (cycles_return.cycles_used pre_ret + cycles_return.cycles_used post_ret)),
      messages := take n (messages S) @ drop (Suc n) (messages S) @ [Response_message orig (Reply (blob_of_candid Candid_empty)) trans_cycles]\<rparr>)))))))"

definition ic_code_upgrade_burned_cycles :: "nat \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> nat" where
  "ic_code_upgrade_burned_cycles n S = (case messages S ! n of Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    let cid = the (candid_parse_cid a) in
    (case candid_parse_cid a of Some cid \<Rightarrow>
    (case (candid_parse_text a [encode_string ''mode''], candid_parse_blob a [encode_string ''wasm_module''], candid_parse_blob a [encode_string ''arg'']) of
      (Some mode, Some w, Some a) \<Rightarrow>
    (case parse_wasm_mod w of Some m \<Rightarrow>
    (case (list_map_get (canisters S) cid, list_map_get (time S) cid, list_map_get (balances S) cid, list_map_get (canister_status S) cid) of
      (Some (Some can), Some t, Some bal, Some can_status) \<Rightarrow>
      let env = \<lparr>env_time = t, balance = bal, freezing_limit = ic_freezing_limit S cid, certificate = None, status = simple_status can_status\<rparr> in
      (case canister_module_pre_upgrade (module can) (wasm_state can, cer, env) of Inr pre_ret \<Rightarrow>
      (case canister_module_post_upgrade m (cid, cycles_return.return pre_ret, a, cer, env) of Inr post_ret \<Rightarrow>
      cycles_return.cycles_used pre_ret + cycles_return.cycles_used post_ret)))))))"

lemma ic_code_upgrade_cycles_inv:
  assumes "ic_code_upgrade_pre n S"
  shows "total_cycles S = total_cycles (ic_code_upgrade_post n S) + ic_code_upgrade_burned_cycles n S"
proof -
  obtain orig cer cee mn a trans_cycles q where msg: "messages S ! n = Call_message orig cer cee mn a trans_cycles q"
    using assms
    by (auto simp: ic_code_upgrade_pre_def split: message.splits)
  define older where "older = take n (messages S)"
  define younger where "younger = drop (Suc n) (messages S)"
  have msgs: "messages S = older @ Call_message orig cer cee mn a trans_cycles q # younger" "(older @ w # younger) ! n = w"
    "take n older = older" "take (n - length older) ws = []" "drop (Suc n) older = []"
    "drop (Suc n - length older) (w # ws) = ws" for w ws
    using id_take_nth_drop[of n "messages S"] assms
    by (auto simp: ic_code_upgrade_pre_def msg younger_def older_def nth_append)
  show ?thesis
    using assms list_map_sum_in_ge[where ?f="balances S" and ?g=id and ?x="the (candid_parse_cid a)"]
    by (auto simp: ic_code_upgrade_pre_def ic_code_upgrade_post_def ic_code_upgrade_burned_cycles_def total_cycles_def Let_def msgs list_map_sum_in[where ?f="balances S"] split: message.splits option.splits sum.splits)
qed



(* System transition: IC Management Canister: Code uninstallation [DONE] *)

definition ic_code_uninstallation_pre :: "nat \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> bool" where
  "ic_code_uninstallation_pre n S = (n < length (messages S) \<and> (case messages S ! n of Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    (q = Unordered \<or> (\<forall>j < n. message_queue (messages S ! j) \<noteq> Some q)) \<and>
    cee = ic_principal \<and>
    mn = encode_string ''uninstall_code'' \<and>
    (case candid_parse_cid a of Some cid \<Rightarrow>
    (case list_map_get (controllers S) cid of Some ctrls \<Rightarrow> cer \<in> ctrls
    | _ \<Rightarrow> False) | _ \<Rightarrow> False)
  | _ \<Rightarrow> False))"

definition ic_code_uninstallation_post :: "nat \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic" where
  "ic_code_uninstallation_post n S = (case messages S ! n of Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    let cid = the (candid_parse_cid a) in
    (case candid_parse_cid a of Some cid \<Rightarrow>
    let call_ctxt_to_msg = (\<lambda>ctxt.
      if call_ctxt_canister ctxt = cid \<and> call_ctxt_needs_to_respond ctxt then
        Some (Response_message (call_ctxt_origin ctxt) (response.Reject CANISTER_REJECT (encode_string ''Canister has been uninstalled'')) (call_ctxt_available_cycles ctxt))
      else None);
    call_ctxt_to_ctxt = (\<lambda>ctxt. if call_ctxt_canister ctxt = cid then call_ctxt_delete ctxt else ctxt) in
    S\<lparr>canisters := list_map_set (canisters S) cid None, certified_data := list_map_set (certified_data S) cid empty_blob,
      messages := take n (messages S) @ drop (Suc n) (messages S) @ [Response_message orig (Reply (blob_of_candid Candid_empty)) trans_cycles] @
        List.map_filter call_ctxt_to_msg (list_map_vals (call_contexts S)),
      call_contexts := list_map_map call_ctxt_to_ctxt (call_contexts S)\<rparr>))"

lemma ic_code_uninstallation_cycles_inv:
  assumes "ic_code_uninstallation_pre n S"
  shows "total_cycles S = total_cycles (ic_code_uninstallation_post n S)"
proof -
  obtain orig cer cee mn a trans_cycles q cid where msg: "messages S ! n = Call_message orig cer cee mn a trans_cycles q"
    and cid_def: "candid_parse_cid a = Some cid"
    using assms
    by (auto simp: ic_code_uninstallation_pre_def split: message.splits option.splits)
  define older where "older = take n (messages S)"
  define younger where "younger = drop (Suc n) (messages S)"
  have msgs: "messages S = older @ Call_message orig cer cee mn a trans_cycles q # younger" "(older @ w # younger) ! n = w"
    "take n older = older" "take (n - length older) ws = []" "drop (Suc n) older = []"
    "drop (Suc n - length older) (w # ws) = ws" for w ws
    using id_take_nth_drop[of n "messages S"] assms
    by (auto simp: ic_code_uninstallation_pre_def msg younger_def older_def nth_append)
  have F1: "list_map_sum_vals call_ctxt_carried_cycles (call_contexts S) =
    list_map_sum_vals id
      (list_map_map (\<lambda>ctxt. if call_ctxt_canister ctxt = cid then call_ctxt_carried_cycles ctxt else 0) (call_contexts S)) +
    list_map_sum_vals call_ctxt_carried_cycles
      (list_map_map (\<lambda>ctxt. if call_ctxt_canister ctxt = cid then call_ctxt_delete ctxt else ctxt) (call_contexts S))"
    using list_map_sum_vals_split[where ?f="call_ctxt_carried_cycles" and ?g="call_ctxt_delete", unfolded call_ctxt_delete_carried_cycles diff_zero]
    by auto
  show ?thesis
    using assms
    by (auto simp: ic_code_uninstallation_pre_def ic_code_uninstallation_post_def total_cycles_def call_ctxt_carried_cycles cid_def Let_def msgs F1
        split: message.splits option.splits sum.splits if_splits intro!: list_map_sum_vals_filter)
qed



(* System transition: IC Management Canister: Stopping a canister (running) [DONE] *)

definition ic_canister_stop_running_pre :: "nat \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> bool" where
  "ic_canister_stop_running_pre n S = (n < length (messages S) \<and> (case messages S ! n of Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    (q = Unordered \<or> (\<forall>j < n. message_queue (messages S ! j) \<noteq> Some q)) \<and>
    cee = ic_principal \<and>
    mn = encode_string ''stop_canister'' \<and>
    (case candid_parse_cid a of Some cid \<Rightarrow>
    (case (list_map_get (canister_status S) cid, list_map_get (controllers S) cid) of (Some Running, Some ctrls) \<Rightarrow>
      cer \<in> ctrls
    | _ \<Rightarrow> False) | _ \<Rightarrow> False)
  | _ \<Rightarrow> False))"

definition ic_canister_stop_running_post :: "nat \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic" where
  "ic_canister_stop_running_post n S = (case messages S ! n of Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    let cid = the (candid_parse_cid a) in
    S\<lparr>canister_status := list_map_set (canister_status S) cid (Stopping [(orig, trans_cycles)]),
      messages := take n (messages S) @ drop (Suc n) (messages S)\<rparr>)"

lemma ic_canister_stop_running_cycles_inv:
  assumes "ic_canister_stop_running_pre n S"
  shows "total_cycles S = total_cycles (ic_canister_stop_running_post n S)"
proof -
  obtain orig cer cee mn a trans_cycles q cid where msg: "messages S ! n = Call_message orig cer cee mn a trans_cycles q"
    and cid_def: "candid_parse_cid a = Some cid"
    using assms
    by (auto simp: ic_canister_stop_running_pre_def split: message.splits option.splits)
  define older where "older = take n (messages S)"
  define younger where "younger = drop (Suc n) (messages S)"
  have msgs: "messages S = older @ Call_message orig cer cee mn a trans_cycles q # younger" "(older @ w # younger) ! n = w"
    "take n older = older" "take (n - length older) ws = []" "drop (Suc n) older = []"
    "drop (Suc n - length older) (w # ws) = ws" for w ws
    using id_take_nth_drop[of n "messages S"] assms
    by (auto simp: ic_canister_stop_running_pre_def msg younger_def older_def nth_append)
  show ?thesis
    using assms
    by (auto simp: ic_canister_stop_running_pre_def ic_canister_stop_running_post_def total_cycles_def call_ctxt_carried_cycles cid_def Let_def msgs
        list_map_sum_in[where ?g=status_cycles] split: message.splits option.splits sum.splits can_status.splits)
qed



(* System transition: IC Management Canister: Stopping a canister (stopping) [DONE] *)

definition ic_canister_stop_stopping_pre :: "nat \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> bool" where
  "ic_canister_stop_stopping_pre n S = (n < length (messages S) \<and> (case messages S ! n of Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    (q = Unordered \<or> (\<forall>j < n. message_queue (messages S ! j) \<noteq> Some q)) \<and>
    cee = ic_principal \<and>
    mn = encode_string ''stop_canister'' \<and>
    (case candid_parse_cid a of Some cid \<Rightarrow>
    (case (list_map_get (canister_status S) cid, list_map_get (controllers S) cid) of (Some (Stopping os), Some ctrls) \<Rightarrow>
      cer \<in> ctrls
    | _ \<Rightarrow> False) | _ \<Rightarrow> False)
  | _ \<Rightarrow> False))"

definition ic_canister_stop_stopping_post :: "nat \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic" where
  "ic_canister_stop_stopping_post n S = (case messages S ! n of Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    let cid = the (candid_parse_cid a) in
    (case list_map_get (canister_status S) cid of Some (Stopping os) \<Rightarrow>
    S\<lparr>canister_status := list_map_set (canister_status S) cid (Stopping (os @ [(orig, trans_cycles)])),
      messages := take n (messages S) @ drop (Suc n) (messages S)\<rparr>))"

lemma ic_canister_stop_stopping_cycles_inv:
  assumes "ic_canister_stop_stopping_pre n S"
  shows "total_cycles S = total_cycles (ic_canister_stop_stopping_post n S)"
proof -
  obtain orig cer cee mn a trans_cycles q cid where msg: "messages S ! n = Call_message orig cer cee mn a trans_cycles q"
    and cid_def: "candid_parse_cid a = Some cid"
    using assms
    by (auto simp: ic_canister_stop_stopping_pre_def split: message.splits option.splits)
  define older where "older = take n (messages S)"
  define younger where "younger = drop (Suc n) (messages S)"
  have msgs: "messages S = older @ Call_message orig cer cee mn a trans_cycles q # younger" "(older @ w # younger) ! n = w"
    "take n older = older" "take (n - length older) ws = []" "drop (Suc n) older = []"
    "drop (Suc n - length older) (w # ws) = ws" for w ws
    using id_take_nth_drop[of n "messages S"] assms
    by (auto simp: ic_canister_stop_stopping_pre_def msg younger_def older_def nth_append)
  show ?thesis
    using assms
    by (auto simp: ic_canister_stop_stopping_pre_def ic_canister_stop_stopping_post_def total_cycles_def call_ctxt_carried_cycles cid_def Let_def msgs
        list_map_sum_in[where ?g=status_cycles] split: message.splits option.splits sum.splits can_status.splits)
qed



(* System transition: IC Management Canister: Stopping a canister (done stopping) [DONE] *)

definition ic_canister_stop_done_stopping_pre :: "'canid \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> bool" where
  "ic_canister_stop_done_stopping_pre cid S =
    (case list_map_get (canister_status S) cid of Some (Stopping os) \<Rightarrow>
      (\<forall>ctxt \<in> list_map_range (call_contexts S). call_ctxt_canister ctxt \<noteq> cid)
    | _ \<Rightarrow> False)"

definition ic_canister_stop_done_stopping_post :: "'canid \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic" where
  "ic_canister_stop_done_stopping_post cid S = (
    let orig_cycles_to_msg = (\<lambda>(or, cyc). Response_message or (Reply (blob_of_candid Candid_empty)) cyc) in
    (case list_map_get (canister_status S) cid of Some (Stopping os) \<Rightarrow>
    S\<lparr>canister_status := list_map_set (canister_status S) cid Stopped,
      messages := messages S @ map orig_cycles_to_msg os\<rparr>))"

lemma ic_canister_stop_done_stopping_cycles_inv:
  assumes "ic_canister_stop_done_stopping_pre cid S"
  shows "total_cycles S = total_cycles (ic_canister_stop_done_stopping_post cid S)"
proof -
  have F1: "(message_cycles \<circ> (\<lambda>(or, y). Response_message or (Reply (blob_of_candid Candid_empty)) y)) = (\<lambda>(or, y). carried_cycles or + y)"
    by auto
  have F2: "(\<Sum>(or, y)\<leftarrow>xs. carried_cycles or + y) = sum_list (map (carried_cycles \<circ> fst) xs) + sum_list (map snd xs)" for xs
    by (induction xs) auto
  show ?thesis
    using assms list_map_sum_in_ge[where ?g=status_cycles and ?f="canister_status S" and ?x=cid]
    by (auto simp: ic_canister_stop_done_stopping_pre_def ic_canister_stop_done_stopping_post_def total_cycles_def call_ctxt_carried_cycles Let_def
        F1 F2 list_map_sum_in[where ?g=status_cycles] split: message.splits option.splits sum.splits can_status.splits)
qed



(* System transition: IC Management Canister: Stopping a canister (stopped) [DONE] *)

definition ic_canister_stop_stopped_pre :: "nat \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> bool" where
  "ic_canister_stop_stopped_pre n S = (n < length (messages S) \<and> (case messages S ! n of Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    (q = Unordered \<or> (\<forall>j < n. message_queue (messages S ! j) \<noteq> Some q)) \<and>
    cee = ic_principal \<and>
    mn = encode_string ''stop_canister'' \<and>
    (case candid_parse_cid a of Some cid \<Rightarrow>
    (case (list_map_get (canister_status S) cid, list_map_get (controllers S) cid) of (Some Stopped, Some ctrls) \<Rightarrow>
      cer \<in> ctrls
    | _ \<Rightarrow> False) | _ \<Rightarrow> False)
  | _ \<Rightarrow> False))"

definition ic_canister_stop_stopped_post :: "nat \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic" where
  "ic_canister_stop_stopped_post n S = (case messages S ! n of Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    let cid = the (candid_parse_cid a) in
    S\<lparr>messages := take n (messages S) @ drop (Suc n) (messages S) @ [Response_message orig (Reply (blob_of_candid Candid_empty)) trans_cycles]\<rparr>)"

lemma ic_canister_stop_stopped_cycles_inv:
  assumes "ic_canister_stop_stopped_pre n S"
  shows "total_cycles S = total_cycles (ic_canister_stop_stopped_post n S)"
proof -
  obtain orig cer cee mn a trans_cycles q cid where msg: "messages S ! n = Call_message orig cer cee mn a trans_cycles q"
    and cid_def: "candid_parse_cid a = Some cid"
    using assms
    by (auto simp: ic_canister_stop_stopped_pre_def split: message.splits option.splits)
  define older where "older = take n (messages S)"
  define younger where "younger = drop (Suc n) (messages S)"
  have msgs: "messages S = older @ Call_message orig cer cee mn a trans_cycles q # younger" "(older @ w # younger) ! n = w"
    "take n older = older" "take (n - length older) ws = []" "drop (Suc n) older = []"
    "drop (Suc n - length older) (w # ws) = ws" for w ws
    using id_take_nth_drop[of n "messages S"] assms
    by (auto simp: ic_canister_stop_stopped_pre_def msg younger_def older_def nth_append)
  show ?thesis
    using assms
    by (auto simp: ic_canister_stop_stopped_pre_def ic_canister_stop_stopped_post_def total_cycles_def call_ctxt_carried_cycles cid_def Let_def msgs
        split: message.splits option.splits sum.splits can_status.splits)
qed



(* System transition: IC Management Canister: Starting a canister (not stopping) [DONE] *)

definition ic_canister_start_not_stopping_pre :: "nat \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> bool" where
  "ic_canister_start_not_stopping_pre n S = (n < length (messages S) \<and> (case messages S ! n of Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    (q = Unordered \<or> (\<forall>j < n. message_queue (messages S ! j) \<noteq> Some q)) \<and>
    cee = ic_principal \<and>
    mn = encode_string ''start_canister'' \<and>
    (case candid_parse_cid a of Some cid \<Rightarrow>
    (case (list_map_get (canister_status S) cid, list_map_get (controllers S) cid) of (Some can_status, Some ctrls) \<Rightarrow>
      (can_status = Running \<or> can_status = Stopped) \<and>
      cer \<in> ctrls
    | _ \<Rightarrow> False) | _ \<Rightarrow> False)
  | _ \<Rightarrow> False))"

definition ic_canister_start_not_stopping_post :: "nat \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic" where
  "ic_canister_start_not_stopping_post n S = (case messages S ! n of Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    let cid = the (candid_parse_cid a) in
    S\<lparr>canister_status := list_map_set (canister_status S) cid Running,
      messages := take n (messages S) @ drop (Suc n) (messages S) @ [Response_message orig (Reply (blob_of_candid Candid_empty)) trans_cycles]\<rparr>)"

lemma ic_canister_start_not_stopping_cycles_inv:
  assumes "ic_canister_start_not_stopping_pre n S"
  shows "total_cycles S = total_cycles (ic_canister_start_not_stopping_post n S)"
proof -
  obtain orig cer cee mn a trans_cycles q cid where msg: "messages S ! n = Call_message orig cer cee mn a trans_cycles q"
    and cid_def: "candid_parse_cid a = Some cid"
    using assms
    by (auto simp: ic_canister_start_not_stopping_pre_def split: message.splits option.splits)
  define older where "older = take n (messages S)"
  define younger where "younger = drop (Suc n) (messages S)"
  have msgs: "messages S = older @ Call_message orig cer cee mn a trans_cycles q # younger" "(older @ w # younger) ! n = w"
    "take n older = older" "take (n - length older) ws = []" "drop (Suc n) older = []"
    "drop (Suc n - length older) (w # ws) = ws" for w ws
    using id_take_nth_drop[of n "messages S"] assms
    by (auto simp: ic_canister_start_not_stopping_pre_def msg younger_def older_def nth_append)
  show ?thesis
    using assms
    by (auto simp: ic_canister_start_not_stopping_pre_def ic_canister_start_not_stopping_post_def total_cycles_def call_ctxt_carried_cycles cid_def Let_def msgs
        list_map_sum_in[where ?g=status_cycles] split: message.splits option.splits sum.splits)
qed



(* System transition: IC Management Canister: Starting a canister (stopping) [DONE] *)

definition ic_canister_start_stopping_pre :: "nat \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> bool" where
  "ic_canister_start_stopping_pre n S = (n < length (messages S) \<and> (case messages S ! n of Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    (q = Unordered \<or> (\<forall>j < n. message_queue (messages S ! j) \<noteq> Some q)) \<and>
    cee = ic_principal \<and>
    mn = encode_string ''start_canister'' \<and>
    (case candid_parse_cid a of Some cid \<Rightarrow>
    (case (list_map_get (canister_status S) cid, list_map_get (controllers S) cid) of (Some (Stopping _), Some ctrls) \<Rightarrow>
      cer \<in> ctrls
    | _ \<Rightarrow> False) | _ \<Rightarrow> False)
  | _ \<Rightarrow> False))"

definition ic_canister_start_stopping_post :: "nat \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic" where
  "ic_canister_start_stopping_post n S = (case messages S ! n of Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    let cid = the (candid_parse_cid a);
    orig_cycles_to_msg = (\<lambda>(or, cyc). Response_message or (response.Reject CANISTER_REJECT (encode_string ''Canister has been restarted'')) cyc) in
    (case list_map_get (canister_status S) cid of Some (Stopping os) \<Rightarrow>
    S\<lparr>canister_status := list_map_set (canister_status S) cid Running,
      messages := take n (messages S) @ drop (Suc n) (messages S) @ [Response_message orig (Reply (blob_of_candid Candid_empty)) trans_cycles] @
      map orig_cycles_to_msg os\<rparr>))"

lemma ic_canister_start_stopping_cycles_inv:
  assumes "ic_canister_start_stopping_pre n S"
  shows "total_cycles S = total_cycles (ic_canister_start_stopping_post n S)"
proof -
  obtain orig cer cee mn a trans_cycles q cid where msg: "messages S ! n = Call_message orig cer cee mn a trans_cycles q"
    and cid_def: "candid_parse_cid a = Some cid"
    using assms
    by (auto simp: ic_canister_start_stopping_pre_def split: message.splits option.splits)
  define older where "older = take n (messages S)"
  define younger where "younger = drop (Suc n) (messages S)"
  have msgs: "messages S = older @ Call_message orig cer cee mn a trans_cycles q # younger" "(older @ w # younger) ! n = w"
    "take n older = older" "take (n - length older) ws = []" "drop (Suc n) older = []"
    "drop (Suc n - length older) (w # ws) = ws" for w ws
    using id_take_nth_drop[of n "messages S"] assms
    by (auto simp: ic_canister_start_stopping_pre_def msg younger_def older_def nth_append)
  have F1: "(message_cycles \<circ> (\<lambda>(or, y). Response_message or (response.Reject CANISTER_REJECT (encode_string ''Canister has been restarted'')) y)) = (\<lambda>(or, y). carried_cycles or + y)"
    by auto
  have F2: "(\<Sum>(or, y)\<leftarrow>xs. carried_cycles or + y) = sum_list (map (carried_cycles \<circ> fst) xs) + sum_list (map snd xs)" for xs
    by (induction xs) auto
  show ?thesis
    using assms list_map_sum_in_ge[where ?g=status_cycles and ?f="canister_status S" and ?x=cid]
    by (auto simp: ic_canister_start_stopping_pre_def ic_canister_start_stopping_post_def total_cycles_def call_ctxt_carried_cycles cid_def Let_def msgs F1 F2
        list_map_sum_in[where ?g=status_cycles and ?f="canister_status S"]
        split: message.splits option.splits sum.splits can_status.splits)
qed



(* System transition: IC Management Canister: Canister deletion [DONE] *)

definition ic_canister_deletion_pre :: "nat \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> bool" where
  "ic_canister_deletion_pre n S = (n < length (messages S) \<and> (case messages S ! n of Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    (q = Unordered \<or> (\<forall>j < n. message_queue (messages S ! j) \<noteq> Some q)) \<and>
    cee = ic_principal \<and>
    mn = encode_string ''delete_canister'' \<and>
    (case candid_parse_cid a of Some cid \<Rightarrow>
    (case (list_map_get (canister_status S) cid, list_map_get (controllers S) cid, list_map_get (balances S) cid) of (Some Stopped, Some ctrls, Some bal) \<Rightarrow>
      cer \<in> ctrls
    | _ \<Rightarrow> False) | _ \<Rightarrow> False)
  | _ \<Rightarrow> False))"

definition ic_canister_deletion_post :: "nat \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic" where
  "ic_canister_deletion_post n S = (case messages S ! n of Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    let cid = the (candid_parse_cid a) in
    S\<lparr>canisters := list_map_del (canisters S) cid,
      controllers := list_map_del (controllers S) cid,
      freezing_threshold := list_map_del (freezing_threshold S) cid,
      canister_status := list_map_del (canister_status S) cid,
      time := list_map_del (time S) cid,
      balances := list_map_del (balances S) cid,
      certified_data := list_map_del (certified_data S) cid,
      messages := take n (messages S) @ drop (Suc n) (messages S) @ [Response_message orig (Reply (blob_of_candid Candid_empty)) trans_cycles]\<rparr>)"

definition ic_canister_deletion_burned_cycles :: "nat \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> nat" where
  "ic_canister_deletion_burned_cycles n S = (case messages S ! n of Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    let cid = the (candid_parse_cid a) in the (list_map_get (balances S) cid))"

lemma ic_canister_deletion_cycles_monotonic:
  assumes "ic_canister_deletion_pre n S"
  shows "total_cycles S = total_cycles (ic_canister_deletion_post n S) + ic_canister_deletion_burned_cycles n S"
proof -
  obtain orig cer cee mn a trans_cycles q cid where msg: "messages S ! n = Call_message orig cer cee mn a trans_cycles q"
    and cid_def: "candid_parse_cid a = Some cid"
    using assms
    by (auto simp: ic_canister_deletion_pre_def split: message.splits option.splits)
  define older where "older = take n (messages S)"
  define younger where "younger = drop (Suc n) (messages S)"
  have msgs: "messages S = older @ Call_message orig cer cee mn a trans_cycles q # younger" "(older @ w # younger) ! n = w"
    "take n older = older" "take (n - length older) ws = []" "drop (Suc n) older = []"
    "drop (Suc n - length older) (w # ws) = ws" for w ws
    using id_take_nth_drop[of n "messages S"] assms
    by (auto simp: ic_canister_deletion_pre_def msg younger_def older_def nth_append)
  show ?thesis
    using assms
    by (auto simp: ic_canister_deletion_pre_def ic_canister_deletion_post_def ic_canister_deletion_burned_cycles_def total_cycles_def call_ctxt_carried_cycles cid_def Let_def msgs
        list_map_del_sum[where ?g=id and ?f="balances S"] list_map_del_sum[where ?g=status_cycles and ?f="canister_status S"]
        split: message.splits option.splits sum.splits can_status.splits)
qed



(* System transition: IC Management Canister: Depositing cycles [DONE] *)

definition ic_depositing_cycles_pre :: "nat \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> bool" where
  "ic_depositing_cycles_pre n S = (n < length (messages S) \<and> (case messages S ! n of Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    (q = Unordered \<or> (\<forall>j < n. message_queue (messages S ! j) \<noteq> Some q)) \<and>
    cee = ic_principal \<and>
    mn = encode_string ''deposit_cycles'' \<and>
    (case candid_parse_cid a of Some cid \<Rightarrow>
    (case list_map_get (balances S) cid of Some bal \<Rightarrow>
      True
    | _ \<Rightarrow> False) | _ \<Rightarrow> False)
  | _ \<Rightarrow> False))"

definition ic_depositing_cycles_post :: "nat \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic" where
  "ic_depositing_cycles_post n S = (case messages S ! n of Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    let cid = the (candid_parse_cid a) in
    (case list_map_get (balances S) cid of Some bal \<Rightarrow>
    S\<lparr>balances := list_map_set (balances S) cid (bal + trans_cycles),
      messages := take n (messages S) @ drop (Suc n) (messages S) @ [Response_message orig (Reply (blob_of_candid Candid_empty)) 0]\<rparr>))"

lemma ic_depositing_cycles_cycles_monotonic:
  assumes "ic_depositing_cycles_pre n S"
  shows "total_cycles S = total_cycles (ic_depositing_cycles_post n S)"
proof -
  obtain orig cer cee mn a trans_cycles q cid where msg: "messages S ! n = Call_message orig cer cee mn a trans_cycles q"
    and cid_def: "candid_parse_cid a = Some cid"
    using assms
    by (auto simp: ic_depositing_cycles_pre_def split: message.splits option.splits)
  define older where "older = take n (messages S)"
  define younger where "younger = drop (Suc n) (messages S)"
  have msgs: "messages S = older @ Call_message orig cer cee mn a trans_cycles q # younger" "(older @ w # younger) ! n = w"
    "take n older = older" "take (n - length older) ws = []" "drop (Suc n) older = []"
    "drop (Suc n - length older) (w # ws) = ws" for w ws
    using id_take_nth_drop[of n "messages S"] assms
    by (auto simp: ic_depositing_cycles_pre_def msg younger_def older_def nth_append)
  show ?thesis
    using assms list_map_sum_in_ge[where ?g=id and ?f="balances S" and ?x=cid]
    by (auto simp: ic_depositing_cycles_pre_def ic_depositing_cycles_post_def total_cycles_def call_ctxt_carried_cycles cid_def Let_def msgs
        list_map_sum_in[where ?g=id and ?f="balances S"] min_def split: message.splits option.splits sum.splits)
qed



(* System transition: IC Management Canister: Random numbers [DONE] *)

definition ic_random_numbers_pre :: "nat \<Rightarrow> 'b \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> bool" where
  "ic_random_numbers_pre n b S = (n < length (messages S) \<and> (case messages S ! n of Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    (q = Unordered \<or> (\<forall>j < n. message_queue (messages S ! j) \<noteq> Some q)) \<and>
    cee = ic_principal \<and>
    mn = encode_string ''raw_rand'' \<and>
    a = blob_of_candid Candid_empty \<and>
    blob_length b = 32
  | _ \<Rightarrow> False))"

definition ic_random_numbers_post :: "nat \<Rightarrow> 'b \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic" where
  "ic_random_numbers_post n b S = (case messages S ! n of Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    S\<lparr>messages := take n (messages S) @ drop (Suc n) (messages S) @ [Response_message orig (Reply (blob_of_candid (Candid_blob b))) trans_cycles]\<rparr>)"

lemma ic_random_numbers_cycles_inv:
  assumes "ic_random_numbers_pre n b S"
  shows "total_cycles S = total_cycles (ic_random_numbers_post n b S)"
proof -
  obtain orig cer cee mn a trans_cycles q where msg: "messages S ! n = Call_message orig cer cee mn a trans_cycles q"
    using assms
    by (auto simp: ic_random_numbers_pre_def split: message.splits)
  define older where "older = take n (messages S)"
  define younger where "younger = drop (Suc n) (messages S)"
  have msgs: "messages S = older @ Call_message orig cer cee mn a trans_cycles q # younger" "(older @ w # younger) ! n = w"
    "take n older = older" "take (n - length older) ws = []" "drop (Suc n) older = []"
    "drop (Suc n - length older) (w # ws) = ws" for w ws
    using id_take_nth_drop[of n "messages S"] assms
    by (auto simp: ic_random_numbers_pre_def msg younger_def older_def nth_append)
  show ?thesis
    using assms
    by (auto simp: ic_random_numbers_pre_def ic_random_numbers_post_def total_cycles_def call_ctxt_carried_cycles Let_def msgs)
qed



(* System transition: IC Management Canister: Canister creation with cycles [DONE] *)

definition ic_provisional_canister_creation_pre :: "nat \<Rightarrow> 'canid \<Rightarrow> nat \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> bool" where
  "ic_provisional_canister_creation_pre n cid t S = (n < length (messages S) \<and> (case messages S ! n of
    Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    (case candid_parse_nat a [encode_string ''amount''] of Some cyc \<Rightarrow>
      (q = Unordered \<or> (\<forall>j < n. message_queue (messages S ! j) \<noteq> Some q)) \<and>
      cee = ic_principal \<and>
      mn = encode_string ''provisional_create_canister_with_cycles'' \<and>
      is_system_assigned (principal_of_canid cid) \<and>
      cid \<notin> list_map_dom (canisters S) \<and>
      cid \<notin> list_map_dom (time S) \<and>
      cid \<notin> list_map_dom (controllers S) \<and>
      cid \<notin> list_map_dom (balances S) \<and>
      cid \<notin> list_map_dom (certified_data S) \<and>
      cid \<notin> list_map_dom (canister_status S)
    | _ \<Rightarrow> False) | _ \<Rightarrow> False))"

definition ic_provisional_canister_creation_post :: "nat \<Rightarrow> 'canid \<Rightarrow> nat \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic" where
  "ic_provisional_canister_creation_post n cid t S = (case messages S ! n of Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    let cyc = the (candid_parse_nat a [encode_string ''amount'']) in
    S\<lparr>canisters := list_map_set (canisters S) cid None,
      time := list_map_set (time S) cid t,
      controllers := list_map_set (controllers S) cid {cer},
      balances := list_map_set (balances S) cid cyc,
      certified_data := list_map_set (certified_data S) cid empty_blob,
      messages := take n (messages S) @ drop (Suc n) (messages S) @ [Response_message orig (Reply (blob_of_candid
        (Candid_record (list_map_init [(encode_string ''canister_id'', Candid_blob (blob_of_canid cid))])))) trans_cycles],
      canister_status := list_map_set (canister_status S) cid Running\<rparr>)"

definition ic_provisional_canister_creation_minted_cycles :: "nat \<Rightarrow> 'canid \<Rightarrow> nat \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> nat" where
  "ic_provisional_canister_creation_minted_cycles n cid t S = (case messages S ! n of Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    the (candid_parse_nat a [encode_string ''amount'']))"

lemma ic_provisional_canister_creation_cycles_antimonotonic:
  assumes "ic_provisional_canister_creation_pre n cid t S"
  shows "total_cycles S + ic_provisional_canister_creation_minted_cycles n cid t S  = total_cycles (ic_provisional_canister_creation_post n cid t S)"
proof -
  obtain orig cer cee mn a trans_cycles q where msg: "messages S ! n = Call_message orig cer cee mn a trans_cycles q"
    using assms
    by (auto simp: ic_provisional_canister_creation_pre_def split: message.splits)
  define older where "older = take n (messages S)"
  define younger where "younger = drop (Suc n) (messages S)"
  have msgs: "messages S = older @ Call_message orig cer cee mn a trans_cycles q # younger" "(older @ w # younger) ! n = w"
    "take n older = older" "take (n - length older) ws = []" "drop (Suc n) older = []"
    "drop (Suc n - length older) (w # ws) = ws" for w ws
    using id_take_nth_drop[of n "messages S"] assms
    by (auto simp: ic_provisional_canister_creation_pre_def msg younger_def older_def nth_append)
  show ?thesis
    using assms
    by (auto simp: ic_provisional_canister_creation_pre_def ic_provisional_canister_creation_post_def ic_provisional_canister_creation_minted_cycles_def total_cycles_def Let_def msgs
        list_map_sum_out[where ?g=id] list_map_sum_out[where ?g=status_cycles] split: message.splits option.splits)
qed



(* System transition: IC Management Canister: Top up canister [DONE] *)

definition ic_top_up_canister_pre :: "nat \<Rightarrow> 'canid \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> bool" where
  "ic_top_up_canister_pre n cid S = (n < length (messages S) \<and> (case messages S ! n of
    Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    (case candid_parse_nat a [encode_string ''amount''] of Some cyc \<Rightarrow>
      (q = Unordered \<or> (\<forall>j < n. message_queue (messages S ! j) \<noteq> Some q)) \<and>
      cee = ic_principal \<and>
      mn = encode_string ''provisional_top_up_canister'' \<and>
      cid \<in> list_map_dom (balances S)
    | _ \<Rightarrow> False) | _ \<Rightarrow> False))"

definition ic_top_up_canister_post :: "nat \<Rightarrow> 'canid \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic" where
  "ic_top_up_canister_post n cid S = (case messages S ! n of Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    let bal = the (list_map_get (balances S) cid);
    cyc = the (candid_parse_nat a [encode_string ''amount'']) in
    S\<lparr>balances := list_map_set (balances S) cid (bal + cyc)\<rparr>)"

definition ic_top_up_canister_minted_cycles :: "nat \<Rightarrow> 'canid \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> nat" where
  "ic_top_up_canister_minted_cycles n cid S = (case messages S ! n of Call_message orig cer cee mn a trans_cycles q \<Rightarrow>
    the (candid_parse_nat a [encode_string ''amount'']))"

lemma ic_top_up_canister_cycles_antimonotonic:
  assumes "ic_top_up_canister_pre n cid S"
  shows "total_cycles S + ic_top_up_canister_minted_cycles n cid S  = total_cycles (ic_top_up_canister_post n cid S)"
proof -
  obtain orig cer cee mn a trans_cycles q where msg: "messages S ! n = Call_message orig cer cee mn a trans_cycles q"
    using assms
    by (auto simp: ic_top_up_canister_pre_def split: message.splits)
  define older where "older = take n (messages S)"
  define younger where "younger = drop (Suc n) (messages S)"
  have msgs: "messages S = older @ Call_message orig cer cee mn a trans_cycles q # younger" "(older @ w # younger) ! n = w"
    "take n older = older" "take (n - length older) ws = []" "drop (Suc n) older = []"
    "drop (Suc n - length older) (w # ws) = ws" for w ws
    using id_take_nth_drop[of n "messages S"] assms
    by (auto simp: ic_top_up_canister_pre_def msg younger_def older_def nth_append)
  show ?thesis
    using assms
    by (cases "list_map_get (balances S) cid")
       (auto simp: ic_top_up_canister_pre_def ic_top_up_canister_post_def ic_top_up_canister_minted_cycles_def total_cycles_def Let_def msgs
        list_map_sum_in[where ?g=id] split: message.splits option.splits)
qed



(* System transition: Callback invocation (not deleted) [DONE] *)

definition callback_invocation_not_deleted_pre :: "nat \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> bool" where
  "callback_invocation_not_deleted_pre n S = (n < length (messages S) \<and> (case messages S ! n of Response_message (From_canister ctxt_id c) resp ref_cycles \<Rightarrow>
    (case list_map_get (call_contexts S) ctxt_id of Some ctxt \<Rightarrow>
      let cid = call_ctxt_canister ctxt in
      (case list_map_get (balances S) cid of Some bal \<Rightarrow> \<not>call_ctxt_deleted ctxt
      | _ \<Rightarrow> False)
    | _ \<Rightarrow> False)
  | _ \<Rightarrow> False))"

definition callback_invocation_not_deleted_post :: "nat \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic" where
  "callback_invocation_not_deleted_post n S = (case messages S ! n of Response_message (From_canister ctxt_id c) resp ref_cycles \<Rightarrow>
    (case list_map_get (call_contexts S) ctxt_id of Some ctxt \<Rightarrow>
      let cid = call_ctxt_canister ctxt in
      (case list_map_get (balances S) cid of Some bal \<Rightarrow>
        S\<lparr>balances := list_map_set (balances S) cid (bal + ref_cycles),
          messages := list_update (messages S) n (Func_message ctxt_id cid (Callback c resp ref_cycles) Unordered)\<rparr>)))"

lemma callback_invocation_not_deleted_cycles_inv:
  assumes "callback_invocation_not_deleted_pre n S"
  shows "total_cycles S = total_cycles (callback_invocation_not_deleted_post n S)"
proof -
  obtain ctxt_id c resp ref_cycles where msg: "messages S ! n = Response_message (From_canister ctxt_id c) resp ref_cycles"
    using assms
    by (auto simp: callback_invocation_not_deleted_pre_def split: message.splits option.splits call_origin.splits)
  define older where "older = take n (messages S)"
  define younger where "younger = drop (Suc n) (messages S)"
  have msgs: "messages S = older @ Response_message (From_canister ctxt_id c) resp ref_cycles # younger" "(older @ w # younger) ! n = w"
    and msgs_upd: "(older @ Response_message (From_canister ctxt_id c) resp ref_cycles # younger)[n := m] = older @ m # younger" for w m
    using assms id_take_nth_drop[of n "messages S"] upd_conv_take_nth_drop[of n "messages S"] assms
    by (auto simp: callback_invocation_not_deleted_pre_def msg older_def younger_def nth_append)
  show ?thesis
    using assms
    by (auto simp: callback_invocation_not_deleted_pre_def callback_invocation_not_deleted_post_def total_cycles_def call_ctxt_carried_cycles Let_def msgs msgs_upd
        list_map_sum_in[where ?g=id and ?f="balances S"] split: option.splits)
qed



(* System transition: Callback invocation (deleted) [DONE] *)

definition callback_invocation_deleted_pre :: "nat \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> bool" where
  "callback_invocation_deleted_pre n S = (n < length (messages S) \<and> (case messages S ! n of Response_message (From_canister ctxt_id c) resp ref_cycles \<Rightarrow>
    (case list_map_get (call_contexts S) ctxt_id of Some ctxt \<Rightarrow>
      let cid = call_ctxt_canister ctxt in
      (case list_map_get (balances S) cid of Some bal \<Rightarrow> call_ctxt_deleted ctxt
      | _ \<Rightarrow> False)
    | _ \<Rightarrow> False)
  | _ \<Rightarrow> False))"

definition callback_invocation_deleted_post :: "nat \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic" where
  "callback_invocation_deleted_post n S = (case messages S ! n of Response_message (From_canister ctxt_id c) resp ref_cycles \<Rightarrow>
    (case list_map_get (call_contexts S) ctxt_id of Some ctxt \<Rightarrow>
      let cid = call_ctxt_canister ctxt in
      (case list_map_get (balances S) cid of Some bal \<Rightarrow>
        S\<lparr>balances := list_map_set (balances S) cid (bal + ref_cycles + MAX_CYCLES_PER_RESPONSE),
          messages := take n (messages S) @ drop (Suc n) (messages S)\<rparr>)))"

lemma callback_invocation_deleted_cycles_inv:
  assumes "callback_invocation_deleted_pre n S"
  shows "total_cycles S = total_cycles (callback_invocation_deleted_post n S)"
proof -
  obtain ctxt_id c resp ref_cycles where msg: "messages S ! n = Response_message (From_canister ctxt_id c) resp ref_cycles"
    using assms
    by (auto simp: callback_invocation_deleted_pre_def split: message.splits option.splits call_origin.splits)
  define older where "older = take n (messages S)"
  define younger where "younger = drop (Suc n) (messages S)"
  have msgs: "messages S = older @ Response_message (From_canister ctxt_id c) resp ref_cycles # younger" "(older @ w # younger) ! n = w"
    "take n older = older" "take (n - length older) ws = []" "drop (Suc n) older = []"
    "drop (Suc n - length older) (w # ws) = ws" for w ws
    using id_take_nth_drop[of n "messages S"] assms
    by (auto simp: callback_invocation_deleted_pre_def msg younger_def older_def nth_append)
  show ?thesis
    using assms
    by (auto simp: callback_invocation_deleted_pre_def callback_invocation_deleted_post_def total_cycles_def call_ctxt_carried_cycles Let_def msgs
        list_map_sum_in[where ?g=id and ?f="balances S"] split: option.splits)
qed



(* System transition: Respond to user request [DONE] *)

definition respond_to_user_request_pre :: "nat \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> bool" where
  "respond_to_user_request_pre n S = (n < length (messages S) \<and> (case messages S ! n of Response_message (From_user req) resp ref_cycles \<Rightarrow>
    (case list_map_get (requests S) req of Some Processing \<Rightarrow>
      True
    | _ \<Rightarrow> False)
  | _ \<Rightarrow> False))"

definition respond_to_user_request_post :: "nat \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic" where
  "respond_to_user_request_post n S = (case messages S ! n of Response_message (From_user req) resp ref_cycles \<Rightarrow>
    let req_resp = (case resp of Reply b \<Rightarrow> Replied b | response.Reject c b \<Rightarrow> Rejected c b) in
    S\<lparr>messages := take n (messages S) @ drop (Suc n) (messages S),
      requests := list_map_set (requests S) req req_resp\<rparr>)"

definition respond_to_user_request_burned_cycles :: "nat \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> nat" where
  "respond_to_user_request_burned_cycles n S = (case messages S ! n of Response_message (From_user req) resp ref_cycles \<Rightarrow>
    ref_cycles)"

lemma respond_to_user_request_cycles_monotonic:
  assumes "respond_to_user_request_pre n S"
  shows "total_cycles S = total_cycles (respond_to_user_request_post n S) + respond_to_user_request_burned_cycles n S"
proof -
  obtain req resp ref_cycles where msg: "messages S ! n = Response_message (From_user req) resp ref_cycles"
    using assms
    by (auto simp: respond_to_user_request_pre_def split: message.splits option.splits call_origin.splits)
  define older where "older = take n (messages S)"
  define younger where "younger = drop (Suc n) (messages S)"
  have msgs: "messages S = older @ Response_message (From_user req) resp ref_cycles # younger" "(older @ w # younger) ! n = w"
    "take n older = older" "take (n - length older) ws = []" "drop (Suc n) older = []"
    "drop (Suc n - length older) (w # ws) = ws" for w ws
    using id_take_nth_drop[of n "messages S"] assms
    by (auto simp: respond_to_user_request_pre_def msg younger_def older_def nth_append)
  show ?thesis
    using assms
    by (auto simp: respond_to_user_request_pre_def respond_to_user_request_post_def respond_to_user_request_burned_cycles_def total_cycles_def call_ctxt_carried_cycles Let_def msgs
        list_map_sum_in[where ?g=id and ?f="balances S"] split: option.splits request_status.splits)
qed



(* System transition: Request clean up [DONE] *)

definition request_cleanup_pre :: "('b, 'p, 'uid, 'canid, 's) request \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> bool" where
  "request_cleanup_pre req S = (case list_map_get (requests S) req of Some req_status \<Rightarrow>
    (case req_status of Replied _ \<Rightarrow> True | Rejected _ _ \<Rightarrow> True | _ \<Rightarrow> False)
    | _ \<Rightarrow> False)"

definition request_cleanup_post :: "('b, 'p, 'uid, 'canid, 's) request \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic" where
  "request_cleanup_post req S = (S\<lparr>requests := list_map_set (requests S) req Done\<rparr>)"

lemma request_cleanup_cycles_inv:
  assumes "request_cleanup_pre n S"
  shows "total_cycles S = total_cycles (request_cleanup_post n S)"
  by (auto simp: request_cleanup_post_def total_cycles_def)



(* System transition: Request clean up (expired) [DONE] *)

definition request_cleanup_expired_pre :: "('b, 'p, 'uid, 'canid, 's) request \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> bool" where
  "request_cleanup_expired_pre req S = (case list_map_get (requests S) req of Some req_status \<Rightarrow>
    (case req_status of Replied _ \<Rightarrow> True | Rejected _ _ \<Rightarrow> True | Done \<Rightarrow> True | _ \<Rightarrow> False) \<and>
    request.ingress_expiry req < system_time S
    | _ \<Rightarrow> False)"

definition request_cleanup_expired_post :: "('b, 'p, 'uid, 'canid, 's) request \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic" where
  "request_cleanup_expired_post req S = (S\<lparr>requests := list_map_del (requests S) req\<rparr>)"

lemma request_cleanup_expired_cycles_inv:
  assumes "request_cleanup_expired_pre n S"
  shows "total_cycles S = total_cycles (request_cleanup_expired_post n S)"
  by (auto simp: request_cleanup_expired_post_def total_cycles_def)



(* System transition: Canister out of cycles [DONE] *)

definition canister_out_of_cycles_pre :: "'canid \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> bool" where
  "canister_out_of_cycles_pre cid S = (case list_map_get (balances S) cid of Some bal \<Rightarrow>
    bal = 0
  | _ \<Rightarrow> False)"

definition canister_out_of_cycles_post :: "'canid \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic" where
  "canister_out_of_cycles_post cid S = (
    let call_ctxt_to_msg = (\<lambda>ctxt.
      if call_ctxt_canister ctxt = cid \<and> call_ctxt_needs_to_respond ctxt then
        Some (Response_message (call_ctxt_origin ctxt) (response.Reject CANISTER_REJECT (encode_string ''Canister has been uninstalled'')) (call_ctxt_available_cycles ctxt))
      else None);
    call_ctxt_to_ctxt = (\<lambda>ctxt. if call_ctxt_canister ctxt = cid then call_ctxt_delete ctxt else ctxt) in
    S\<lparr>canisters := list_map_set (canisters S) cid None, certified_data := list_map_set (certified_data S) cid empty_blob,
      messages := messages S @ List.map_filter call_ctxt_to_msg (list_map_vals (call_contexts S)),
      call_contexts := list_map_map call_ctxt_to_ctxt (call_contexts S)\<rparr>)"

lemma canister_out_of_cycles_cycles_inv:
  assumes "canister_out_of_cycles_pre cid S"
  shows "total_cycles S = total_cycles (canister_out_of_cycles_post cid S)"
proof -
  have F1: "list_map_sum_vals call_ctxt_carried_cycles (call_contexts S) =
    list_map_sum_vals id
      (list_map_map (\<lambda>ctxt. if call_ctxt_canister ctxt = cid then call_ctxt_carried_cycles ctxt else 0) (call_contexts S)) +
    list_map_sum_vals call_ctxt_carried_cycles
      (list_map_map (\<lambda>ctxt. if call_ctxt_canister ctxt = cid then call_ctxt_delete ctxt else ctxt) (call_contexts S))"
    using list_map_sum_vals_split[where ?f="call_ctxt_carried_cycles" and ?g="call_ctxt_delete", unfolded call_ctxt_delete_carried_cycles diff_zero]
    by auto
  show ?thesis
    using assms
    by (auto simp: canister_out_of_cycles_pre_def canister_out_of_cycles_post_def total_cycles_def call_ctxt_carried_cycles Let_def F1
        split: message.splits option.splits sum.splits if_splits intro!: list_map_sum_vals_filter)
qed



(* System transition: Time progressing and cycle consumption (canister time) [DONE] *)

definition canister_time_progress_pre :: "'canid \<Rightarrow> nat \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> bool" where
  "canister_time_progress_pre cid t1 S = (case list_map_get (time S) cid of Some t0 \<Rightarrow>
      t0 < t1
    | _ \<Rightarrow> False)"

definition canister_time_progress_post :: "'canid \<Rightarrow> nat \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic" where
  "canister_time_progress_post cid t1 S = (S\<lparr>time := list_map_set (time S) cid t1\<rparr>)"

lemma canister_time_progress_cycles_inv:
  assumes "canister_time_progress_pre cid t1 S"
  shows "total_cycles S = total_cycles (canister_time_progress_post cid t1 S)"
  by (auto simp: canister_time_progress_post_def total_cycles_def)



(* System transition: Time progressing and cycle consumption (cycle consumption) [DONE] *)

definition cycle_consumption_pre :: "'canid \<Rightarrow> nat \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> bool" where
  "cycle_consumption_pre cid b1 S = (case list_map_get (balances S) cid of Some b0 \<Rightarrow>
      0 \<le> b1 \<and> b1 < b0
    | _ \<Rightarrow> False)"

definition cycle_consumption_post :: "'canid \<Rightarrow> nat \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic" where
  "cycle_consumption_post cid b1 S = (S\<lparr>balances := list_map_set (balances S) cid b1\<rparr>)"

definition cycle_consumption_burned_cycles :: "'canid \<Rightarrow> nat \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> nat" where
  "cycle_consumption_burned_cycles cid b1 S = the (list_map_get (balances S) cid) - b1"

lemma cycle_consumption_cycles_monotonic:
  assumes "cycle_consumption_pre cid b1 S"
  shows "total_cycles S = total_cycles (cycle_consumption_post cid b1 S) + cycle_consumption_burned_cycles cid b1 S"
  using assms list_map_sum_in_ge[where ?g=id and ?f="balances S" and ?x=cid]
  by (auto simp: cycle_consumption_pre_def cycle_consumption_post_def cycle_consumption_burned_cycles_def total_cycles_def
      list_map_sum_in[where ?g=id and ?f="balances S"] split: option.splits)



(* System transition: Time progressing and cycle consumption (system time) [DONE] *)

definition system_time_progress_pre :: "nat \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> bool" where
  "system_time_progress_pre t1 S = (system_time S < t1)"

definition system_time_progress_post :: "nat \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic" where
  "system_time_progress_post t1 S = (S\<lparr>system_time := t1\<rparr>)"

lemma system_time_progress_cycles_inv:
  assumes "system_time_progress_pre t1 S"
  shows "total_cycles S = total_cycles (system_time_progress_post t1 S)"
  by (auto simp: system_time_progress_post_def total_cycles_def)



(* State machine *)

inductive ic_steps :: "'sig itself \<Rightarrow> 'sd itself \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow>
  nat \<Rightarrow> nat \<Rightarrow> ('p, 'uid, 'canid, 'b, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> bool" where
  "ic_steps sig sd S 0 0 S"
| request_submission: "ic_steps sig sd S0 minted burned S \<Longrightarrow> request_submission_pre (E :: ('b, 'p, 'uid, 'canid, 's, 'pk, 'sig, 'sd) envelope) S \<Longrightarrow> ic_steps sig sd S0 minted (burned + request_submission_burned_cycles E S) (request_submission_post E S)"
| request_rejection: "ic_steps sig sd S0 minted burned S \<Longrightarrow> request_rejection_pre (E :: ('b, 'p, 'uid, 'canid, 's, 'pk, 'sig, 'sd) envelope) req code msg S \<Longrightarrow> ic_steps sig sd S0 minted burned (request_rejection_post E req code msg S)"
| initiate_canister_call: "ic_steps sig sd S0 minted burned S \<Longrightarrow> initiate_canister_call_pre req S \<Longrightarrow> ic_steps sig sd S0 minted burned (initiate_canister_call_post req S)"
| call_reject: "ic_steps sig sd S0 minted burned S \<Longrightarrow> call_reject_pre n S \<Longrightarrow> ic_steps sig sd S0 minted burned (call_reject_post n S)"
| call_context_create: "ic_steps sig sd S0 minted burned S \<Longrightarrow> call_context_create_pre n ctxt_id S \<Longrightarrow> ic_steps sig sd S0 minted burned (call_context_create_post n ctxt_id S)"
| call_context_heartbeat: "ic_steps sig sd S0 minted burned S \<Longrightarrow> call_context_heartbeat_pre cee ctxt_id S \<Longrightarrow> ic_steps sig sd S0 minted burned (call_context_heartbeat_post cee ctxt_id S)"
| message_execution: "ic_steps sig sd S0 minted burned S \<Longrightarrow> message_execution_pre n S \<Longrightarrow> ic_steps sig sd S0 minted (burned + message_execution_burned_cycles n S) (message_execution_post n S)"
| call_context_starvation: "ic_steps sig sd S0 minted burned S \<Longrightarrow> call_context_starvation_pre ctxt_id S \<Longrightarrow> ic_steps sig sd S0 minted burned (call_context_starvation_post ctxt_id S)"
| call_context_removal: "ic_steps sig sd S0 minted burned S \<Longrightarrow> call_context_removal_pre ctxt_id S \<Longrightarrow> ic_steps sig sd S0 minted (burned + call_context_removal_burned_cycles ctxt_id S) (call_context_removal_post ctxt_id S)"
| ic_canister_creation: "ic_steps sig sd S0 minted burned S \<Longrightarrow> ic_canister_creation_pre n cid t S \<Longrightarrow> ic_steps sig sd S0 minted burned (ic_canister_creation_post n cid t S)"
| ic_update_settings: "ic_steps sig sd S0 minted burned S \<Longrightarrow> ic_update_settings_pre n S \<Longrightarrow> ic_steps sig sd S0 minted burned (ic_update_settings_post n S)"
| ic_canister_status: "ic_steps sig sd S0 minted burned S \<Longrightarrow> ic_canister_status_pre n m S \<Longrightarrow> ic_steps sig sd S0 minted burned (ic_canister_status_post n m S)"
| ic_code_installation: "ic_steps sig sd S0 minted burned S \<Longrightarrow> ic_code_installation_pre n S \<Longrightarrow> ic_steps sig sd S0 minted (burned + ic_code_installation_burned_cycles n S) (ic_code_installation_post n S)"
| ic_code_upgrade: "ic_steps sig sd S0 minted burned S \<Longrightarrow> ic_code_upgrade_pre n S \<Longrightarrow> ic_steps sig sd S0 minted (burned + ic_code_upgrade_burned_cycles n S) (ic_code_upgrade_post n S)"
| ic_code_uninstallation: "ic_steps sig sd S0 minted burned S \<Longrightarrow> ic_code_uninstallation_pre n S \<Longrightarrow> ic_steps sig sd S0 minted burned (ic_code_uninstallation_post n S)"
| ic_canister_stop_running: "ic_steps sig sd S0 minted burned S \<Longrightarrow> ic_canister_stop_running_pre n S \<Longrightarrow> ic_steps sig sd S0 minted burned (ic_canister_stop_running_post n S)"
| ic_canister_stop_stopping: "ic_steps sig sd S0 minted burned S \<Longrightarrow> ic_canister_stop_stopping_pre n S \<Longrightarrow> ic_steps sig sd S0 minted burned (ic_canister_stop_stopping_post n S)"
| ic_canister_stop_done_stopping: "ic_steps sig sd S0 minted burned S \<Longrightarrow> ic_canister_stop_done_stopping_pre cid S \<Longrightarrow> ic_steps sig sd S0 minted burned (ic_canister_stop_done_stopping_post cid S)"
| ic_canister_stop_stopped: "ic_steps sig sd S0 minted burned S \<Longrightarrow> ic_canister_stop_stopped_pre n S \<Longrightarrow> ic_steps sig sd S0 minted burned (ic_canister_stop_stopped_post n S)"
| ic_canister_start_not_stopping: "ic_steps sig sd S0 minted burned S \<Longrightarrow> ic_canister_start_not_stopping_pre n S \<Longrightarrow> ic_steps sig sd S0 minted burned (ic_canister_start_not_stopping_post n S)"
| ic_canister_start_stopping: "ic_steps sig sd S0 minted burned S \<Longrightarrow> ic_canister_start_stopping_pre n S \<Longrightarrow> ic_steps sig sd S0 minted burned (ic_canister_start_stopping_post n S)"
| ic_canister_deletion: "ic_steps sig sd S0 minted burned S \<Longrightarrow> ic_canister_deletion_pre n S \<Longrightarrow> ic_steps sig sd S0 minted (burned + ic_canister_deletion_burned_cycles n S) (ic_canister_deletion_post n S)"
| ic_depositing_cycles: "ic_steps sig sd S0 minted burned S \<Longrightarrow> ic_depositing_cycles_pre n S \<Longrightarrow> ic_steps sig sd S0 minted burned (ic_depositing_cycles_post n S)"
| ic_random_numbers: "ic_steps sig sd S0 minted burned S \<Longrightarrow> ic_random_numbers_pre n b S \<Longrightarrow> ic_steps sig sd S0 minted burned (ic_random_numbers_post n b S)"
| ic_provisional_canister_creation: "ic_steps sig sd S0 minted burned S \<Longrightarrow> ic_provisional_canister_creation_pre n cid t S \<Longrightarrow> ic_steps sig sd S0 (minted + ic_provisional_canister_creation_minted_cycles n cid t S) burned (ic_provisional_canister_creation_post n cid t S)"
| ic_top_up_canister: "ic_steps sig sd S0 minted burned S \<Longrightarrow> ic_top_up_canister_pre n cid S \<Longrightarrow> ic_steps sig sd S0 (minted + ic_top_up_canister_minted_cycles n cid S) burned (ic_top_up_canister_post n cid S)"
| callback_invocation_not_deleted: "ic_steps sig sd S0 minted burned S \<Longrightarrow> callback_invocation_not_deleted_pre n S \<Longrightarrow> ic_steps sig sd S0 minted burned (callback_invocation_not_deleted_post n S)"
| callback_invocation_deleted: "ic_steps sig sd S0 minted burned S \<Longrightarrow> callback_invocation_deleted_pre n S \<Longrightarrow> ic_steps sig sd S0 minted burned (callback_invocation_deleted_post n S)"
| respond_to_user_request: "ic_steps sig sd S0 minted burned S \<Longrightarrow> respond_to_user_request_pre n S \<Longrightarrow> ic_steps sig sd S0 minted (burned + respond_to_user_request_burned_cycles n S) (respond_to_user_request_post n S)"
| request_cleanup: "ic_steps sig sd S0 minted burned S \<Longrightarrow> request_cleanup_pre req S \<Longrightarrow> ic_steps sig sd S0 minted burned (request_cleanup_post req S)"
| request_cleanup_expired: "ic_steps sig sd S0 minted burned S \<Longrightarrow> request_cleanup_expired_pre req S \<Longrightarrow> ic_steps sig sd S0 minted burned (request_cleanup_expired_post req S)"
| canister_out_of_cycles: "ic_steps sig sd S0 minted burned S \<Longrightarrow> canister_out_of_cycles_pre cid S \<Longrightarrow> ic_steps sig sd S0 minted burned (canister_out_of_cycles_post cid S)"
| canister_time_progress: "ic_steps sig sd S0 minted burned S \<Longrightarrow> canister_time_progress_pre cid t1 S \<Longrightarrow> ic_steps sig sd S0 minted burned (canister_time_progress_post cid t1 S)"
| cycle_consumption: "ic_steps sig sd S0 minted burned S \<Longrightarrow> cycle_consumption_pre cid b1 S \<Longrightarrow> ic_steps sig sd S0 minted (burned + cycle_consumption_burned_cycles cid b1 S) (cycle_consumption_post cid b1 S)"
| system_time_progress: "ic_steps sig sd S0 minted burned S \<Longrightarrow> system_time_progress_pre t1 S \<Longrightarrow> ic_steps sig sd S0 minted burned (system_time_progress_post t1 S)"

lemma total_cycles_monotonic:
  assumes "ic_steps TYPE('sig) TYPE('sd) S0 minted burned S"
  shows "total_cycles S0 + minted = total_cycles S + burned"
  using assms
  apply (induction "TYPE('sig)" "TYPE('sd)" S0 minted burned S rule: ic_steps.induct)
                      apply auto[1]
  using request_submission_cycles_inv apply fastforce
  using request_rejection_cycles_inv apply fastforce
  using initiate_canister_call_cycles_inv apply fastforce
  using call_reject_cycles_inv apply fastforce
  using call_context_create_cycles_inv apply fastforce
  using call_context_heartbeat_cycles_inv apply fastforce
  using message_execution_cycles_monotonic apply fastforce
  using call_context_starvation_cycles_inv apply fastforce
  using call_context_removal_cycles_monotonic apply fastforce
  using ic_canister_creation_cycles_inv apply fastforce
  using ic_update_settings_cycles_inv apply fastforce
  using ic_canister_status_cycles_inv apply fastforce
  using ic_code_installation_cycles_inv apply fastforce
  using ic_code_upgrade_cycles_inv apply fastforce
  using ic_code_uninstallation_cycles_inv apply fastforce
  using ic_canister_stop_running_cycles_inv apply fastforce
  using ic_canister_stop_stopping_cycles_inv apply fastforce
  using ic_canister_stop_done_stopping_cycles_inv apply fastforce
  using ic_canister_stop_stopped_cycles_inv apply fastforce
  using ic_canister_start_not_stopping_cycles_inv apply fastforce
  using ic_canister_start_stopping_cycles_inv apply fastforce
  using ic_canister_deletion_cycles_monotonic apply fastforce
  using ic_depositing_cycles_cycles_monotonic apply fastforce
  using ic_random_numbers_cycles_inv apply fastforce
  using ic_provisional_canister_creation_cycles_antimonotonic apply fastforce
  using ic_top_up_canister_cycles_antimonotonic apply fastforce
  using callback_invocation_not_deleted_cycles_inv apply fastforce
  using callback_invocation_deleted_cycles_inv apply fastforce
  using respond_to_user_request_cycles_monotonic apply fastforce
  using request_cleanup_cycles_inv apply fastforce
  using request_cleanup_expired_cycles_inv apply fastforce
  using canister_out_of_cycles_cycles_inv apply fastforce
  using canister_time_progress_cycles_inv apply fastforce
  using cycle_consumption_cycles_monotonic apply fastforce
  using system_time_progress_cycles_inv apply fastforce
  done

end

export_code request_submission_pre request_submission_post
  request_rejection_pre request_rejection_post
  initiate_canister_call_pre initiate_canister_call_post
  call_reject_pre call_reject_post
  call_context_create_pre call_context_create_post
  call_context_heartbeat_pre call_context_heartbeat_post
  message_execution_pre message_execution_post
  call_context_starvation_pre call_context_starvation_post
  call_context_removal_pre call_context_removal_post
  ic_canister_creation_pre ic_canister_creation_post
  ic_update_settings_pre ic_update_settings_post
  ic_canister_status_pre ic_canister_status_post
  ic_code_installation_pre ic_code_installation_post
  ic_code_upgrade_pre ic_code_upgrade_post
  ic_code_uninstallation_pre ic_code_uninstallation_post
  ic_canister_stop_running_pre ic_canister_stop_running_post
  ic_canister_stop_stopping_pre ic_canister_stop_stopping_post
  ic_canister_stop_done_stopping_pre ic_canister_stop_done_stopping_post
  ic_canister_stop_stopped_pre ic_canister_stop_stopped_post
  ic_canister_start_not_stopping_pre ic_canister_start_not_stopping_post
  ic_canister_start_stopping_pre ic_canister_start_stopping_post
  ic_canister_deletion_pre ic_canister_deletion_post
  ic_depositing_cycles_pre ic_depositing_cycles_post
  ic_random_numbers_pre ic_random_numbers_post
  ic_provisional_canister_creation_pre ic_provisional_canister_creation_post
  ic_top_up_canister_pre ic_top_up_canister_post
  callback_invocation_not_deleted_pre callback_invocation_not_deleted_post
  callback_invocation_deleted_pre callback_invocation_deleted_post
  respond_to_user_request_pre respond_to_user_request_post
  request_cleanup_pre request_cleanup_post
  request_cleanup_expired_pre request_cleanup_expired_post
  canister_out_of_cycles_pre canister_out_of_cycles_post
  canister_time_progress_pre canister_time_progress_post
  cycle_consumption_pre cycle_consumption_post
  system_time_progress_pre system_time_progress_post
in Haskell module_name IC file_prefix code

end
