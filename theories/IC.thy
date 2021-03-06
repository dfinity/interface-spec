theory IC
  imports "HOL-Library.AList"
begin

(* Partial maps *)

typedef ('a, 'b) list_map = "{f :: ('a \<times> 'b) list. distinct (map fst f)}"
  by (auto intro: exI[of _ "[]"])

setup_lifting type_definition_list_map

lift_definition list_map_dom :: "('a, 'b) list_map \<Rightarrow> 'a set" is
  "set \<circ> map fst" .

lift_definition list_map_vals :: "('a, 'b) list_map \<Rightarrow> 'b set" is
  "set \<circ> map snd" .

lift_definition list_map_sum_vals :: "('b \<Rightarrow> nat) \<Rightarrow> ('a, 'b) list_map \<Rightarrow> nat" is
  "\<lambda>g. sum_list \<circ> (map (g \<circ> snd))" .

lift_definition list_map_get :: "('a, 'b) list_map \<Rightarrow> 'a \<Rightarrow> 'b option" is
  "map_of" .

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

record ('b, 'p) arg =
  data :: 'b
  caller :: 'p

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
  method_name :: 's
  arg :: 'b
  transferred_cycles :: nat
  callback :: 'c

record ('w, 'p, 'canid, 's, 'b, 'c) update_return =
  new_state :: 'w
  new_calls :: "('p, 'canid, 's, 'b, 'c) method_call list"
  new_certified_data :: "'b option"
  response :: "('b, 's) response option"
  cycles_accepted :: nat
type_synonym ('w, 'p, 'canid, 's, 'b, 'c, 'tr) update_func = "'w \<Rightarrow> 'tr + ('w, 'p, 'canid, 's, 'b, 'c) update_return"
type_synonym ('w, 'b, 's, 'tr) query_func = "'w \<Rightarrow> 'tr + ('b, 's) response"

type_synonym available_cycles = nat
type_synonym refunded_cycles = nat

datatype inspect_method_result = Accept | Reject
record ('p, 'canid, 'b, 'tr, 'w, 'sm, 'c, 's) canister_module_rec =
  init :: "'canid \<times> ('b, 'p) arg \<times> 'b env \<Rightarrow> 'tr + 'w"
  pre_upgrade :: "'w \<times> 'p \<times> 'b env \<Rightarrow> 'tr + 'sm"
  post_upgrade :: "'canid \<times> 'sm \<times> ('b, 'p) arg \<times> 'b env \<Rightarrow> 'tr + 'w"
  update_methods :: "('s, (('b, 'p) arg \<times> 'b env \<times> available_cycles) \<Rightarrow> ('w, 'p, 'canid, 's, 'b, 'c, 'tr) update_func) list_map"
  query_methods :: "('s, (('b, 'p) arg \<times> 'b env) \<Rightarrow> ('w, 'b, 's, 'tr) query_func) list_map"
  heartbeat :: "'b env \<Rightarrow> 'w \<Rightarrow> 'tr + 'w"
  callbacks :: "('c \<times> ('b, 's) response \<times> refunded_cycles \<times> 'b env \<times> available_cycles) \<Rightarrow> ('w, 'p, 'canid, 's, 'b, 'c, 'tr) update_func"
  inspect_message :: "('s \<times> 'w \<times> ('b, 'p) arg \<times> 'b env) \<Rightarrow> 'tr + inspect_method_result"
typedef ('p, 'canid, 'b, 'tr, 'w, 'sm, 'c, 's) canister_module =
  "{m :: ('p, 'canid, 'b, 'tr, 'w, 'sm, 'c, 's) canister_module_rec. list_map_dom (update_methods m) \<inter> list_map_dom (query_methods m) = {}}"
  by (auto intro: exI[of _ "\<lparr>init = undefined, pre_upgrade = undefined, post_upgrade = undefined,
      update_methods = list_map_empty, query_methods = list_map_empty, heartbeat = undefined, callbacks = undefined,
      inspect_message = undefined\<rparr>"])

setup_lifting type_definition_canister_module

lift_definition dispatch_method :: "'s \<Rightarrow> ('p, 'canid, 'b, 'tr, 'w, 'sm, 'c, 's) canister_module \<Rightarrow>
  (((('b, 'p) arg \<times> 'b env \<times> available_cycles) \<Rightarrow> ('w, 'p, 'canid, 's, 'b, 'c, 'tr) update_func) +
   ((('b, 'p) arg \<times> 'b env) \<Rightarrow> ('w, 'b, 's, 'tr) query_func)) option" is
  "\<lambda>f m. case list_map_get (update_methods m) f of Some f' \<Rightarrow> None | None \<Rightarrow> (case list_map_get (query_methods m) f of Some f' \<Rightarrow> None | None \<Rightarrow> None)" .

lift_definition canister_module_callbacks :: "('p, 'canid, 'b, 'tr, 'w, 'sm, 'c, 's) canister_module \<Rightarrow>
  ('c \<times> ('b, 's) response \<times> refunded_cycles \<times> 'b env \<times> available_cycles) \<Rightarrow> ('w, 'p, 'canid, 's, 'b, 'c, 'tr) update_func" is
  callbacks .

lift_definition canister_module_heartbeat :: "('p, 'canid, 'b, 'tr, 'w, 'sm, 'c, 's) canister_module \<Rightarrow> 'b env \<Rightarrow> 'w \<Rightarrow> 'tr + 'w" is
  heartbeat .

(* Call contexts *)

record ('b, 'p, 'uid, 'canid, 's) request =
  nonce :: 'b
  ingress_expiry :: nat
  sender :: 'uid
  canister_id :: 'canid
  method_name :: 's
  data :: 'b
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

lift_definition call_ctxt_origin :: "('p, 'uid, 'canid, 'b, 's, 'c, 'cid) call_ctxt \<Rightarrow> ('b, 'p, 'uid, 'canid, 's, 'c, 'cid) call_origin" is
  "\<lambda>ctxt. origin ctxt" .

lift_definition call_ctxt_needs_to_respond :: "('p, 'uid, 'canid, 'b, 's, 'c, 'cid) call_ctxt \<Rightarrow> bool" is
  "\<lambda>ctxt. needs_to_respond ctxt" .

lift_definition call_ctxt_available_cycles :: "('p, 'uid, 'canid, 'b, 's, 'c, 'cid) call_ctxt \<Rightarrow> nat" is
  "\<lambda>ctxt. available_cycles ctxt" .

lemma call_ctxt_inv: "\<not>call_ctxt_needs_to_respond x2 \<Longrightarrow> call_ctxt_available_cycles x2 = 0"
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

(* Calls and Messages *)

datatype 'canid queue_origin = System | Canister 'canid
datatype 'canid queue = Unordered | Queue "'canid queue_origin" 'canid
datatype ('s, 'p, 'b, 'c) entry_point =
  Public_method "'s" "'p" "'b"
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
  data :: 'b
type_synonym ('b, 'uid, 'canid, 's) APIReadRequest = "('b, 'uid) StateRead + ('b, 'uid, 'canid, 's) CanisterQuery"
record ('b, 'p, 'uid, 'canid, 's, 'pk, 'sig, 'sd) envelope =
  content :: "('b, 'p, 'uid, 'canid, 's) request + ('b, 'uid, 'canid, 's) APIReadRequest"
  sender_pubkey :: "'pk option"
  sender_sig :: "'sig option"
  sender_delegation :: 'sd

datatype ('b, 's) request_status = Received | Processing | Rejected reject_code 's | Replied 'b | Done

(* The system state *)

record ('p, 'canid, 'b, 'tr, 'w, 'sm, 'c, 's) can_state_rec =
  wasm_state :: 'w
  module :: "('p, 'canid, 'b, 'tr, 'w, 'sm, 'c, 's) canister_module"
  raw_module :: 'b
  public_custom_sections :: "('s, 'b) list_map"
  private_custom_sections :: "('s, 'b) list_map"
type_synonym ('p, 'canid, 'b, 'tr, 'w, 'sm, 'c, 's) can_state = "('p, 'canid, 'b, 'tr, 'w, 'sm, 'c, 's) can_state_rec option"
datatype ('b, 'p, 'uid, 'canid, 's, 'c, 'cid) can_status = Running | Stopping "(('b, 'p, 'uid, 'canid, 's, 'c, 'cid) call_origin \<times> nat) list" | Stopped
record ('p, 'uid, 'canid, 'b, 'tr, 'w, 'sm, 'c, 's, 'cid, 'pk) ic =
  requests :: "(('b, 'p, 'uid, 'canid, 's) request, ('b, 's) request_status) list_map"
  canisters :: "('canid, ('p, 'canid, 'b, 'tr, 'w, 'sm, 'c, 's) can_state) list_map"
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

(* State transitions *)

context fixes
  CANISTER_ERROR :: reject_code
  and SYS_FATAL :: reject_code
  and SYS_TRANSIENT :: reject_code
  and MAX_CYCLES_PER_MESSAGE :: nat
  and MAX_CYCLES_PER_RESPONSE :: nat
  and MAX_CANISTER_BALANCE :: nat
  and ic_freezing_limit :: "('p, 'uid, 'canid, 'b, 'tr, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> 'canid \<Rightarrow> nat"
  and encode_string :: "string \<Rightarrow> 's"
  and principal_of_uid :: "'uid \<Rightarrow> 'p"
  and principal_of_canid :: "'canid \<Rightarrow> 'p"
begin

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

lift_definition call_ctxt_carried_cycles :: "('p, 'uid, 'canid, 'b, 's, 'c, 'cid) call_ctxt \<Rightarrow> nat" is
  "\<lambda>ctxt. (if needs_to_respond ctxt
    then available_cycles ctxt + carried_cycles (origin ctxt)
    else 0)" .

lemma call_ctxt_respond_carried_cycles[simp]: "call_ctxt_carried_cycles (call_ctxt_respond ctxt) = 0"
  by transfer auto

lemma call_ctxt_carried_cycles: "call_ctxt_carried_cycles ctxt = (if call_ctxt_needs_to_respond ctxt
  then call_ctxt_available_cycles ctxt + carried_cycles (call_ctxt_origin ctxt) else 0)"
  by transfer auto

definition total_cycles :: "('p, 'uid, 'canid, 'b, 'tr, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> nat" where
  "total_cycles ic = (
    let cycles_in_balances = list_map_sum_vals id (balances ic) in
    let cycles_in_messages = sum_list (map message_cycles (messages ic)) in
    let cycles_in_contexts = list_map_sum_vals call_ctxt_carried_cycles (call_contexts ic) in
    cycles_in_balances + cycles_in_messages + cycles_in_contexts)"

(* Accessor functions *)

fun calling_context :: "('b, 'p, 'uid, 'canid, 's, 'c, 'cid) call_origin \<Rightarrow> 'cid option" where
  "calling_context (From_canister c _) = Some c"
| "calling_context _ = None"

fun message_queue :: "('b, 'p, 'uid, 'canid, 's, 'c, 'cid) message \<Rightarrow> 'canid queue option" where
  "message_queue (Call_message _ _ _ _ _ _ q) = Some q"
| "message_queue (Func_message _ _ _ q) = Some q"
| "message_queue _ = None"

(* Type conversion functions *)

fun to_status :: "('b, 'p, 'uid, 'canid, 's, 'c, 'cid) can_status \<Rightarrow> status" where
  "to_status can_status.Running = status.Running"
| "to_status (can_status.Stopping _) = status.Stopping"
| "to_status can_status.Stopped = status.Stopped"



(* System transition: API Request submission [DONE] *)

definition request_submission_pre :: "('b, 'p, 'uid, 'canid, 's, 'pk, 'sig, 'sd) envelope \<Rightarrow> ('p, 'uid, 'canid, 'b, 'tr, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> bool" where
  "request_submission_pre E S = (case content E of Inl req \<Rightarrow> req \<notin> list_map_dom (requests S) | _ \<Rightarrow> False)"

definition request_submission_post :: "('b, 'p, 'uid, 'canid, 's, 'pk, 'sig, 'sd) envelope \<Rightarrow> ('p, 'uid, 'canid, 'b, 'tr, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> ('p, 'uid, 'canid, 'b, 'tr, 'w, 'sm, 'c, 's, 'cid, 'pk) ic" where
  "request_submission_post E S = S\<lparr>requests := list_map_set (requests S) (projl (content E)) Received\<rparr>"

lemma request_submission_cycles_inv:
  "request_submission_pre E S \<Longrightarrow> total_cycles S = total_cycles (request_submission_post E S)"
  by (auto simp: request_submission_pre_def request_submission_post_def total_cycles_def)



(* System transition: Request rejection [DONE] *)

definition request_rejection_pre :: "('b, 'p, 'uid, 'canid, 's, 'pk, 'sig, 'sd) envelope \<Rightarrow> ('b, 'p, 'uid, 'canid, 's) request \<Rightarrow> reject_code \<Rightarrow> 's \<Rightarrow> ('p, 'uid, 'canid, 'b, 'tr, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> bool" where
  "request_rejection_pre E req code msg S = (list_map_get (requests S) req = Some Received \<and> (code = SYS_FATAL \<or> code = SYS_TRANSIENT))"

definition request_rejection_post :: "('b, 'p, 'uid, 'canid, 's, 'pk, 'sig, 'sd) envelope \<Rightarrow> ('b, 'p, 'uid, 'canid, 's) request \<Rightarrow> reject_code \<Rightarrow> 's \<Rightarrow> ('p, 'uid, 'canid, 'b, 'tr, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> ('p, 'uid, 'canid, 'b, 'tr, 'w, 'sm, 'c, 's, 'cid, 'pk) ic" where
  "request_rejection_post E req code msg S = S\<lparr>requests := list_map_set (requests S) req (Rejected code msg)\<rparr>"

lemma request_rejection_cycles_inv:
  "request_rejection_pre E req code msg S \<Longrightarrow> total_cycles S = total_cycles (request_rejection_post E req code msg S)"
  by (auto simp: request_rejection_pre_def request_rejection_post_def total_cycles_def)



(* System transition: Initiating canister calls [DONE] *)

definition initiate_canister_call_pre :: "('b, 'p, 'uid, 'canid, 's) request \<Rightarrow>
  ('p, 'uid, 'canid, 'b, 'tr, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> bool" where
  "initiate_canister_call_pre req S = (list_map_get (requests S) req = Some Received \<and>
    system_time S \<le> request.ingress_expiry req \<and>
    request.canister_id req \<in> list_map_dom (canisters S))"

definition initiate_canister_call_post :: "('b, 'p, 'uid, 'canid, 's) request \<Rightarrow>
  ('p, 'uid, 'canid, 'b, 'tr, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow>
  ('p, 'uid, 'canid, 'b, 'tr, 'w, 'sm, 'c, 's, 'cid, 'pk) ic" where
  "initiate_canister_call_post req S =
    S\<lparr>requests := list_map_set (requests S) req Processing, messages :=
      Call_message (From_user req) (principal_of_uid (request.sender req)) (request.canister_id req) (request.method_name req)
      (request.data req) 0 Unordered # messages S\<rparr>"

lemma initiate_canister_call_cycles_inv:
  "initiate_canister_call_pre R S \<Longrightarrow>
  total_cycles S = total_cycles (initiate_canister_call_post R S)"
  by (auto simp: initiate_canister_call_pre_def initiate_canister_call_post_def total_cycles_def)



(* System transition: Calls to stopped/stopping/frozen canisters are rejected [DONE] *)

definition call_reject_pre :: "nat \<Rightarrow> ('p, 'uid, 'canid, 'b, 'tr, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> bool" where
  "call_reject_pre n S = (n < length (messages S) \<and> (case messages S ! n of
    Call_message orig cer cee mn d trans_cycles q \<Rightarrow>
      (q = Unordered \<or> (\<forall>j < n. message_queue (messages S ! j) \<noteq> Some q)) \<and>
      (case list_map_get (canister_status S) cee of Some Stopped \<Rightarrow> True
      | Some (Stopping l) \<Rightarrow> True
      | _ \<Rightarrow> (case list_map_get (balances S) cee of Some bal \<Rightarrow> bal < ic_freezing_limit S cee | _ \<Rightarrow> False))
    | _ \<Rightarrow> False))"

definition call_reject_post :: "nat \<Rightarrow> ('p, 'uid, 'canid, 'b, 'tr, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> ('p, 'uid, 'canid, 'b, 'tr, 'w, 'sm, 'c, 's, 'cid, 'pk) ic" where
  "call_reject_post n S = (case messages S ! n of Call_message orig cer cee mn d trans_cycles q \<Rightarrow>
    S\<lparr>messages := take n (messages S) @ drop (Suc n) (messages S) @ [Response_message orig (response.Reject CANISTER_ERROR (encode_string ''canister not running'')) trans_cycles]\<rparr>)"

lemma call_reject_cycles_inv:
  assumes "call_reject_pre n S"
  shows "total_cycles S = total_cycles (call_reject_post n S)"
proof -
  obtain orig cer cee mn d trans_cycles q where msg: "messages S ! n = Call_message orig cer cee mn d trans_cycles q"
    using assms
    by (auto simp: call_reject_pre_def split: message.splits)
  define older where "older = take n (messages S)"
  define younger where "younger = drop (Suc n) (messages S)"
  have msgs: "messages S = older @ Call_message orig cer cee mn d trans_cycles q # younger" "(older @ w # younger) ! n = w"
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
  \<Rightarrow> ('p, 'uid, 'canid, 'b, 'tr, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> bool" where
  "call_context_create_pre n ctxt_id S = (n < length (messages S) \<and> (case messages S ! n of
    Call_message orig cer cee mn d trans_cycles q \<Rightarrow>
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

definition call_context_create_post :: "nat \<Rightarrow> 'cid \<Rightarrow> ('p, 'uid, 'canid, 'b, 'tr, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> ('p, 'uid, 'canid, 'b, 'tr, 'w, 'sm, 'c, 's, 'cid, 'pk) ic" where
  "call_context_create_post n ctxt_id S = (case messages S ! n of Call_message orig cer cee mn d trans_cycles q \<Rightarrow>
    case list_map_get (balances S) cee of Some bal \<Rightarrow>
    S\<lparr>messages := list_update (messages S) n (Func_message ctxt_id cee (Public_method mn cer d) q),
      call_contexts := list_map_set (call_contexts S) ctxt_id (create_call_ctxt cee orig trans_cycles),
      balances := list_map_set (balances S) cee (bal - MAX_CYCLES_PER_MESSAGE)\<rparr>)"

lemma call_context_create_cycles_inv:
  assumes "call_context_create_pre n ctxt_id S"
  shows "total_cycles S = total_cycles (call_context_create_post n ctxt_id S)"
proof -
  obtain orig cer cee mn d trans_cycles q where msg: "messages S ! n = Call_message orig cer cee mn d trans_cycles q"
    using assms
    by (auto simp: call_context_create_pre_def split: message.splits)
  define xs where "xs = take n (messages S)"
  define older where "older = drop (Suc n) (messages S)"
  have msgs: "messages S = xs @ Call_message orig cer cee mn d trans_cycles q # older" "(xs @ m # older) ! n = m"
    and msgs_upd: "(xs @ Call_message orig cer cee mn d trans_cycles q # older)[n := m] = xs @ m # older" for m
    using id_take_nth_drop[of n "messages S"] upd_conv_take_nth_drop[of n "messages S"] assms
    by (auto simp: call_context_create_pre_def msg xs_def older_def nth_append)
  show ?thesis
    using assms list_map_sum_in_ge[of "balances S" cee, where ?g=id]
    by (auto simp: call_context_create_pre_def call_context_create_post_def total_cycles_def
        list_map_sum_in[where ?g=id, simplified] list_map_sum_out msgs msgs_upd split: option.splits)
qed



(* System transition: Call context creation: Heartbeat [DONE] *)

definition call_context_heartbeat_pre :: "'canid \<Rightarrow> 'cid \<Rightarrow> ('p, 'uid, 'canid, 'b, 'tr, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> bool" where
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

definition call_context_heartbeat_post :: "'canid \<Rightarrow> 'cid \<Rightarrow> ('p, 'uid, 'canid, 'b, 'tr, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> ('p, 'uid, 'canid, 'b, 'tr, 'w, 'sm, 'c, 's, 'cid, 'pk) ic" where
  "call_context_heartbeat_post cee ctxt_id S =
  (case list_map_get (balances S) cee of Some bal \<Rightarrow>
    S\<lparr>messages := Func_message ctxt_id cee Heartbeat (Queue System cee) # messages S,
    call_contexts := list_map_set (call_contexts S) ctxt_id (create_call_ctxt_heartbeat cee),
    balances := list_map_set (balances S) cee (bal - MAX_CYCLES_PER_MESSAGE)\<rparr>)"

lemma call_context_heartbeat_cycles_inv:
  "call_context_heartbeat_pre cee ctxt_id S \<Longrightarrow>
    total_cycles S = total_cycles (call_context_heartbeat_post cee ctxt_id S)"
  using list_map_sum_in_ge[of "balances S" cee, where ?g=id, simplified]
  by (auto simp: call_context_heartbeat_pre_def call_context_heartbeat_post_def total_cycles_def
      list_map_sum_in[where ?g=id, simplified] list_map_sum_out split: option.splits)



(* System transition: Message execution [DONE] *)

fun query_as_update :: "((('b, 'p) arg \<times> 'b env) \<Rightarrow> ('w, 'b, 's, 'tr) query_func) \<times> ('b, 'p) arg \<times> 'b env \<Rightarrow> ('w, 'p, 'canid, 's, 'b, 'c, 'tr) update_func" where
  "query_as_update (f, a, e) = (\<lambda>w. case f (a, e) w of Inl t \<Rightarrow> Inl t |
    Inr res \<Rightarrow> Inr \<lparr>new_state = w, new_calls = [], new_certified_data = None, response = Some res, cycles_accepted = 0\<rparr>)"

fun heartbeat_as_update :: "('b env \<Rightarrow> 'w \<Rightarrow> 'tr + 'w) \<times> 'b env \<Rightarrow> ('w, 'p, 'canid, 's, 'b, 'c, 'tr) update_func" where
  "heartbeat_as_update (f, e) w = (case f e w of Inl t \<Rightarrow> Inl t |
    Inr w' \<Rightarrow> Inr \<lparr>update_return.new_state = w', update_return.new_calls = [], update_return.new_certified_data = None,
      update_return.response = None, update_return.cycles_accepted = 0\<rparr>)"

fun exec_function :: "('s, 'p, 'b, 'c) entry_point \<Rightarrow> 'b env \<Rightarrow> nat \<Rightarrow> ('p, 'canid, 'b, 'tr, 'w, 'sm, 'c, 's) canister_module \<Rightarrow> ('w, 'p, 'canid, 's, 'b, 'c, 'tr) update_func" where
  "exec_function (entry_point.Public_method mn c d) e bal m = (
    let arg = \<lparr>arg.data = d, arg.caller = c\<rparr> in
    case dispatch_method mn m of Some (Inl upd) \<Rightarrow> upd (arg, e, bal)
    | Some (Inr query) \<Rightarrow> query_as_update (query, arg, e) | None \<Rightarrow>
    undefined)"
| "exec_function (entry_point.Callback cb resp ref_cycles) e bal m =
    canister_module_callbacks m (cb, resp, ref_cycles, e, bal)"
| "exec_function (entry_point.Heartbeat) e bal m = heartbeat_as_update ((canister_module_heartbeat m), e)"

definition message_execution_pre :: "nat \<Rightarrow> nat \<Rightarrow> ('p, 'uid, 'canid, 'b, 'tr, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> bool" where
  "message_execution_pre n cycles_used S =
    (n < length (messages S) \<and> (case messages S ! n of Func_message ctxt_id recv ep q \<Rightarrow>
    (q = Unordered \<or> (\<forall>j < n. message_queue (messages S ! j) \<noteq> Some q)) \<and>
    (case (list_map_get (canisters S) recv, list_map_get (balances S) recv, list_map_get (canister_status S) recv,
      list_map_get (time S) recv, list_map_get (call_contexts S) ctxt_id) of
      (Some (Some can), Some bal, Some can_status, Some t, Some ctxt) \<Rightarrow> True | _ \<Rightarrow> False)
    | _ \<Rightarrow> False))"

definition message_execution_post :: "nat \<Rightarrow> nat \<Rightarrow> ('p, 'uid, 'canid, 'b, 'tr, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> ('p, 'uid, 'canid, 'b, 'tr, 'w, 'sm, 'c, 's, 'cid, 'pk) ic" where
  "message_execution_post n cycles_used S = (case messages S ! n of Func_message ctxt_id recv ep q \<Rightarrow>
    (case (list_map_get (canisters S) recv, list_map_get (balances S) recv, list_map_get (canister_status S) recv,
      list_map_get (time S) recv, list_map_get (call_contexts S) ctxt_id) of
      (Some (Some can), Some bal, Some can_status, Some t, Some ctxt) \<Rightarrow> (
        let Mod = module can;
        Is_response = (case ep of Callback _ _ _ \<Rightarrow> True | _ \<Rightarrow> False);
        Env = \<lparr>env_time = t, balance = bal, freezing_limit = ic_freezing_limit S recv, certificate = None, status = to_status can_status\<rparr>;
        Available = call_ctxt_available_cycles ctxt;
        F = exec_function ep Env Available Mod;
        R = F (wasm_state can);
        (cycles_accepted_res, new_calls_res) = (case R of Inr res \<Rightarrow> (cycles_accepted res, new_calls res));
        New_balance = bal + cycles_accepted_res + (if Is_response then MAX_CYCLES_PER_RESPONSE else MAX_CYCLES_PER_MESSAGE)
          - (cycles_used + sum_list (map (\<lambda>x. MAX_CYCLES_PER_RESPONSE + transferred_cycles x) new_calls_res));
        no_response = (case R of Inr result \<Rightarrow> update_return.response result = None) in
        if \<not>isl R \<and> cycles_used \<le> (if Is_response then MAX_CYCLES_PER_RESPONSE else MAX_CYCLES_PER_MESSAGE) \<and>
          cycles_accepted_res \<le> Available \<and>
          cycles_used + sum_list (map (\<lambda>x. MAX_CYCLES_PER_RESPONSE + transferred_cycles x) new_calls_res) \<le>
            bal + cycles_accepted_res + (if Is_response then MAX_CYCLES_PER_RESPONSE else MAX_CYCLES_PER_MESSAGE) \<and>
          New_balance > (if Is_response then 0 else ic_freezing_limit S recv) \<and>
          (no_response \<or> call_ctxt_needs_to_respond ctxt) then
          (let result = projr R;
            new_call_to_message = (\<lambda>call. Call_message (From_canister ctxt_id (callback call)) (principal_of_canid recv)
              (callee call) (method_call.method_name call) (arg call) (transferred_cycles call) (Queue (Canister recv) (callee call)));
            response_messages = (case response result of None \<Rightarrow> []
              | Some resp \<Rightarrow> [Response_message (call_ctxt_origin ctxt) resp (Available - cycles_accepted_res)]);
            messages = take n (messages S) @ drop (Suc n) (messages S) @ map new_call_to_message new_calls_res @ response_messages;
            new_ctxt = (case response result of
              None \<Rightarrow> call_ctxt_deduct_cycles cycles_accepted_res ctxt
            | Some _ \<Rightarrow> call_ctxt_respond ctxt);
            certified_data = (case new_certified_data result of None \<Rightarrow> certified_data S
              | Some cd \<Rightarrow> list_map_set (certified_data S) recv cd)
            in S\<lparr>canisters := list_map_set (canisters S) recv (Some (can\<lparr>wasm_state := new_state result\<rparr>)),
              messages := messages, call_contexts := list_map_set (call_contexts S) ctxt_id new_ctxt,
              balances := list_map_set (balances S) recv New_balance, certified_data := certified_data\<rparr>)
        else S\<lparr>messages := take n (messages S) @ drop (Suc n) (messages S),
            balances := list_map_set (balances S) recv (bal + ((if Is_response then MAX_CYCLES_PER_RESPONSE else MAX_CYCLES_PER_MESSAGE) - cycles_used))\<rparr>))
    | _ \<Rightarrow> undefined)"

definition message_execution_lost_cycles :: "nat \<Rightarrow> nat \<Rightarrow> ('p, 'uid, 'canid, 'b, 'tr, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> nat" where
  "message_execution_lost_cycles n cycles_used S = (case messages S ! n of Func_message ctxt_id recv ep q \<Rightarrow>
    let Is_response = (case ep of Callback _ _ _ \<Rightarrow> True | _ \<Rightarrow> False) in
    min cycles_used (if Is_response then MAX_CYCLES_PER_RESPONSE else MAX_CYCLES_PER_MESSAGE))"

lemma message_execution_cycles_monotonic:
  assumes pre: "message_execution_pre n cycles_used S"
  shows "total_cycles S = total_cycles (message_execution_post n cycles_used S) + message_execution_lost_cycles n cycles_used S"
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
  define Env :: "'b env" where "Env = \<lparr>env_time = t, balance = bal, freezing_limit = ic_freezing_limit S recv, certificate = None, status = to_status can_status\<rparr>"
  define Available where "Available = call_ctxt_available_cycles ctxt"
  define F where "F = exec_function ep Env Available Mod"
  define R where "R = F (wasm_state can)"
  obtain cycles_accepted_res new_calls_res where res: "(cycles_accepted_res, new_calls_res) = (case R of Inr res \<Rightarrow> (cycles_accepted res, new_calls res))"
    by (cases "(case R of Inr res \<Rightarrow> (cycles_accepted res, new_calls res))") auto
  define New_balance where "New_balance = bal + cycles_accepted_res + (if Is_response then MAX_CYCLES_PER_RESPONSE else MAX_CYCLES_PER_MESSAGE)
    - (cycles_used + sum_list (map (\<lambda>x. MAX_CYCLES_PER_RESPONSE + transferred_cycles x) new_calls_res))"
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
    balances := list_map_set (balances S) recv (bal + ((if Is_response then MAX_CYCLES_PER_RESPONSE else MAX_CYCLES_PER_MESSAGE) - cycles_used))\<rparr>"
  define cond where "cond = (\<not>isl R \<and> cycles_used \<le> (if Is_response then MAX_CYCLES_PER_RESPONSE else MAX_CYCLES_PER_MESSAGE) \<and>
    cycles_accepted_res \<le> Available \<and>
    cycles_used + sum_list (map (\<lambda>x. MAX_CYCLES_PER_RESPONSE + transferred_cycles x) new_calls_res) \<le>
      bal + cycles_accepted_res + (if Is_response then MAX_CYCLES_PER_RESPONSE else MAX_CYCLES_PER_MESSAGE) \<and>
    New_balance > (if Is_response then 0 else ic_freezing_limit S recv) \<and>
    (no_response \<or> call_ctxt_needs_to_respond ctxt))"
  have reserved: "(if Is_response then MAX_CYCLES_PER_RESPONSE else MAX_CYCLES_PER_MESSAGE) = cycles_reserved ep"
    by (auto simp: Is_response_def split: entry_point.splits)
  show ?thesis
  proof (cases cond)
    case False
    have "message_execution_post n cycles_used S = S''"
      "message_execution_lost_cycles n cycles_used S = min cycles_used (if Is_response then MAX_CYCLES_PER_RESPONSE else MAX_CYCLES_PER_MESSAGE)"
      using False
      by (simp_all add: message_execution_post_def message_execution_lost_cycles_def Let_def msg prod
          Mod_def[symmetric] Is_response_def[symmetric] Env_def[symmetric] Available_def[symmetric] F_def[symmetric] R_def[symmetric] res[symmetric]
          New_balance_def[symmetric] no_response_def[symmetric] S''_def[symmetric] cond_def[symmetric] del: min_less_iff_conj split del: if_split)
    then show ?thesis
      using lm(2)
      by (auto simp: total_cycles_def S''_def msgs lm(1) reserved)
  next
    case True
    define result where "result = projr R"
    have R_Inr: "R = Inr result"
      using True
      by (auto simp: cond_def result_def)
    define response_messages where "response_messages = (case response result of None \<Rightarrow> []
      | Some resp \<Rightarrow> [Response_message (call_ctxt_origin ctxt) resp (Available - cycles_accepted_res)])"
    define new_call_to_message :: "(?'p, 'canid, 's, 'b, 'c) method_call \<Rightarrow> ('b, 'p, 'uid, 'canid, 's, 'c, 'cid) message" where
      "new_call_to_message = (\<lambda>call. Call_message (From_canister ctxt_id (callback call)) (principal_of_canid recv)
        (callee call) (method_call.method_name call) (arg call) (transferred_cycles call) (Queue (Canister recv) (callee call)))"
    define messages where "messages = take n (ic.messages S) @ drop (Suc n) (ic.messages S) @ map new_call_to_message new_calls_res @ response_messages"
    define new_ctxt where "new_ctxt = (case response result of
        None \<Rightarrow> call_ctxt_deduct_cycles cycles_accepted_res ctxt
      | Some _ \<Rightarrow> call_ctxt_respond ctxt)"
    define certified_data where "certified_data = (case new_certified_data result of None \<Rightarrow> ic.certified_data S
      | Some cd \<Rightarrow> list_map_set (ic.certified_data S) recv cd)"
    define S' where "S' = S\<lparr>canisters := list_map_set (canisters S) recv (Some (can\<lparr>wasm_state := new_state result\<rparr>)),
      messages := messages, call_contexts := list_map_set (call_contexts S) ctxt_id new_ctxt,
      balances := list_map_set (balances S) recv New_balance, certified_data := certified_data\<rparr>"
    have cycles_accepted_res_def: "cycles_accepted_res = cycles_accepted result"
      and new_calls_res_def: "new_calls_res = new_calls result"
      using res
      by (auto simp: R_Inr)
    have no_response: "no_response = (response result = None)"
      by (auto simp: no_response_def R_Inr)
    have msg_exec: "message_execution_post n cycles_used S = S'"
      and lost: "message_execution_lost_cycles n cycles_used S = min cycles_used (if Is_response then MAX_CYCLES_PER_RESPONSE else MAX_CYCLES_PER_MESSAGE)"
      using True
      by (simp_all add: message_execution_post_def message_execution_lost_cycles_def Let_def msg prod
          Mod_def[symmetric] Is_response_def[symmetric] Env_def[symmetric] Available_def[symmetric] F_def[symmetric] R_def[symmetric] res[symmetric]
          New_balance_def[symmetric] no_response_def[symmetric] S''_def[symmetric] cond_def[symmetric]
          messages_def[symmetric] new_ctxt_def[symmetric] certified_data_def[symmetric] S'_def[symmetric]
          result_def[symmetric] response_messages_def[symmetric] new_call_to_message_def[symmetric]
          del: min_less_iff_conj split del: if_split)
    have "message_cycles \<circ> new_call_to_message = (\<lambda>c. MAX_CYCLES_PER_RESPONSE + transferred_cycles c)" for c :: "(?'p, 'canid, 's, 'b, 'c) method_call"
      by (auto simp: new_call_to_message_def)
    then have A1: "sum_list (map (message_cycles \<circ> new_call_to_message) new_calls_res) = (\<Sum>x\<leftarrow>new_calls_res. MAX_CYCLES_PER_RESPONSE + transferred_cycles x)"
      by auto
    have A2: "sum_list (map local.message_cycles response_messages) = (case response result of None \<Rightarrow> 0
      | _ \<Rightarrow> carried_cycles (call_ctxt_origin ctxt) + (call_ctxt_available_cycles ctxt - cycles_accepted result))"
      by (auto simp: response_messages_def Available_def cycles_accepted_res_def split: option.splits)
    have A3: "call_ctxt_carried_cycles new_ctxt = (case response result of Some _ \<Rightarrow> 0
      | _ \<Rightarrow> if call_ctxt_needs_to_respond ctxt then carried_cycles (call_ctxt_origin ctxt) + (call_ctxt_available_cycles ctxt - cycles_accepted result) else 0)"
      by (auto simp: new_ctxt_def Available_def cycles_accepted_res_def call_ctxt_carried_cycles split: option.splits)
    have A4: "call_ctxt_carried_cycles ctxt = (if call_ctxt_needs_to_respond ctxt then carried_cycles (call_ctxt_origin ctxt) + call_ctxt_available_cycles ctxt else 0)"
      using call_ctxt_carried_cycles
      by auto
    have reserve: "cycles_reserved ep = (if Is_response then MAX_CYCLES_PER_RESPONSE else MAX_CYCLES_PER_MESSAGE)"
      by (auto simp: Is_response_def split: entry_point.splits)
    have messages_msgs: "messages = older @ younger @ map new_call_to_message new_calls_res @ response_messages"
      by (auto simp: messages_def older_def younger_def)
    show ?thesis
      using lm(2,4) True call_ctxt_inv[of ctxt]
      by (auto simp: cond_def msg_exec S'_def total_cycles_def lm(1,3) msgs messages_msgs A1 A2 A3 A4 New_balance_def
          reserve cycles_accepted_res_def no_response_def R_Inr lost Available_def split: option.splits)
  qed
qed



(* System transition: Call context starvation [DONE] *)

definition call_context_starvation_pre :: "'cid \<Rightarrow> ('p, 'uid, 'canid, 'b, 'tr, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> bool" where
  "call_context_starvation_pre ctxt_id S =
  (case list_map_get (call_contexts S) ctxt_id of Some call_context \<Rightarrow> call_ctxt_needs_to_respond call_context \<and>
    call_ctxt_origin call_context \<noteq> From_heartbeat \<and>
    (\<forall>msg \<in> set (messages S). case msg of
        Call_message orig _ _ _ _ _ _ \<Rightarrow> calling_context orig \<noteq> Some ctxt_id
      | Response_message orig _ _ \<Rightarrow> calling_context orig \<noteq> Some ctxt_id
      | _ \<Rightarrow> True) \<and>
    (\<forall>other_call_context \<in> list_map_vals (call_contexts S).
      call_ctxt_needs_to_respond other_call_context \<longrightarrow>
      calling_context (call_ctxt_origin other_call_context) \<noteq> Some ctxt_id)
  | None \<Rightarrow> False)"

definition call_context_starvation_post :: "'cid \<Rightarrow>
  ('p, 'uid, 'canid, 'b, 'tr, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> ('p, 'uid, 'canid, 'b, 'tr, 'w, 'sm, 'c, 's, 'cid, 'pk) ic" where
  "call_context_starvation_post ctxt_id S = (
    case list_map_get (call_contexts S) ctxt_id of Some call_context \<Rightarrow>
    let msg = Response_message (call_ctxt_origin call_context) (response.Reject CANISTER_ERROR (encode_string ''starvation'')) (call_ctxt_available_cycles call_context)
    in S\<lparr>call_contexts := list_map_set (call_contexts S) ctxt_id (call_ctxt_respond call_context),
        messages := messages S @ [msg]\<rparr>)"

lemma call_context_starvation_cycles_inv:
  "call_context_starvation_pre ctxt_id S \<Longrightarrow>
  total_cycles S = total_cycles (call_context_starvation_post ctxt_id S)"
  using list_map_sum_in_ge[where ?f="call_contexts S" and ?x=ctxt_id and ?g=call_ctxt_carried_cycles]
  by (auto simp: call_context_starvation_pre_def call_context_starvation_post_def total_cycles_def
      call_ctxt_carried_cycles list_map_sum_in[where ?g=call_ctxt_carried_cycles] split: option.splits)



(* System transition: Call context removal [DONE] *)

definition call_context_removal_pre :: "'cid \<Rightarrow> ('p, 'uid, 'canid, 'b, 'tr, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> bool" where
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
      (\<forall>other_call_context \<in> list_map_vals (call_contexts S).
        call_ctxt_needs_to_respond other_call_context \<longrightarrow>
        calling_context (call_ctxt_origin other_call_context) \<noteq> Some ctxt_id)
    | None \<Rightarrow> False))"

definition call_context_removal_post :: "'cid \<Rightarrow>
  ('p, 'uid, 'canid, 'b, 'tr, 'w, 'sm, 'c, 's, 'cid, 'pk) ic \<Rightarrow> ('p, 'uid, 'canid, 'b, 'tr, 'w, 'sm, 'c, 's, 'cid, 'pk) ic" where
  "call_context_removal_post ctxt_id S = S\<lparr>call_contexts := list_map_del (call_contexts S) ctxt_id\<rparr>"

lemma call_context_removal_cycles_inv:
  "call_context_removal_pre ctxt_id S \<Longrightarrow>
  total_cycles S = total_cycles (call_context_removal_post ctxt_id S) +
    (case list_map_get (call_contexts S) ctxt_id of Some call_context \<Rightarrow> call_ctxt_available_cycles call_context)"
  using call_ctxt_inv
  by (auto simp: call_context_removal_pre_def call_context_removal_post_def total_cycles_def call_ctxt_carried_cycles list_map_del_sum split: option.splits)

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
in Haskell module_name IC file_prefix code

end
