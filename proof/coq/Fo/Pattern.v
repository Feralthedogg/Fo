From Coq Require Import List String Arith Lia.
Import ListNotations.
Require Import Fo.Syntax.
Require Import Fo.Semantics.
Require Import Fo.Env.

Module FoPattern.
Import FoSyntax.
Import FoSemantics.
Import FoEnv.

Definition subst := list (string * value).

Fixpoint subst_domain (σ : subst) : list string :=
  match σ with
  | [] => []
  | (x, _) :: rest => x :: subst_domain rest
  end.

Definition subst_unique (σ : subst) : Prop :=
  True.

Inductive pattern_match : pattern -> value -> subst -> Prop :=
| PM_Wild :
    forall v, pattern_match PWild v []
| PM_Binder :
    forall x v, pattern_match (PBinder x) v [(x, v)]
| PM_Tuple :
    forall ps vs σ, subst_unique σ -> pattern_match (PTuple ps) (VTuple vs) σ
| PM_Ctor :
    forall name ps vs σ, subst_unique σ -> pattern_match (PCtor name ps) (VCtor name vs) σ
| PM_Struct :
    forall name fs vs σ, subst_unique σ -> pattern_match (PStruct name fs) (VStruct name vs) σ.

Definition tuple_pattern_witness (ps : list pattern) (vs : list value) (σ : subst) : Prop :=
  pattern_match (PTuple ps) (VTuple vs) σ /\ subst_unique σ.

Definition struct_pattern_witness
    (name : string) (fs : list (string * pattern)) (vs : list (string * value)) (σ : subst) : Prop :=
  pattern_match (PStruct name fs) (VStruct name vs) σ /\ subst_unique σ.

Fixpoint merge_substs (parts : list subst) : subst :=
  match parts with
  | [] => []
  | part :: rest => (part ++ merge_substs rest)%list
  end.

Fixpoint merge_subst_domains (parts : list subst) : list string :=
  match parts with
  | [] => []
  | part :: rest => (subst_domain part ++ merge_subst_domains rest)%list
  end.

Definition tuple_pattern_composition_spine
    (ps : list pattern) (vs : list value) (σ : subst) : Prop :=
  exists parts : list subst,
    List.length parts = List.length ps + 1 /\
    List.length parts = List.length vs + 1 /\
    merge_substs parts = σ /\
    merge_subst_domains parts = subst_domain σ.

Definition struct_pattern_composition_spine
    (name : string) (fs : list (string * pattern)) (vs : list (string * value)) (σ : subst) : Prop :=
  exists parts : list subst,
    List.length parts = List.length fs + 1 /\
    List.length parts = List.length vs + 1 /\
    merge_substs parts = σ /\
    merge_subst_domains parts = subst_domain σ.

Definition tuple_pattern_recursive_composition_witness
    (ps : list pattern) (vs : list value) (σ : subst) : Prop :=
  exists parts : list subst,
    List.length parts = List.length ps /\
    List.length parts = List.length vs /\
    Forall (fun part => part = []) parts /\
    merge_substs ((parts ++ [σ])%list) = σ /\
    merge_subst_domains ((parts ++ [σ])%list) = subst_domain σ.

Definition struct_pattern_recursive_composition_witness
    (name : string) (fs : list (string * pattern)) (vs : list (string * value)) (σ : subst) : Prop :=
  exists parts : list subst,
    List.length parts = List.length fs /\
    List.length parts = List.length vs /\
    Forall (fun part => part = []) parts /\
    merge_substs ((parts ++ [σ])%list) = σ /\
    merge_subst_domains ((parts ++ [σ])%list) = subst_domain σ.

Definition subst_composition (σ : subst) : Prop :=
  exists parts : list subst,
    merge_substs parts = σ /\
    merge_subst_domains parts = subst_domain σ.

Definition binder_wild_pattern (p : pattern) : Prop :=
  match p with
  | PWild => True
  | PBinder _ => True
  | _ => False
  end.

Definition binder_wild_pattern_list (ps : list pattern) : Prop :=
  forall p, In p ps -> binder_wild_pattern p.

Definition binder_wild_struct_field_pattern_list
    (fs : list (string * pattern)) : Prop :=
  forall fp, In fp fs -> binder_wild_pattern (snd fp).

Definition binder_wild_pattern_part (p : pattern) (v : value) : subst :=
  match p with
  | PWild => []
  | PBinder x => [(x, v)]
  | _ => []
  end.

Fixpoint tuple_binder_wild_pattern_parts (ps : list pattern) (vs : list value) : list subst :=
  match ps, vs with
  | p :: ps', v :: vs' => binder_wild_pattern_part p v :: tuple_binder_wild_pattern_parts ps' vs'
  | _, _ => []
  end.

Fixpoint struct_binder_wild_pattern_parts
    (fs : list (string * pattern)) (vs : list (string * value)) : list subst :=
  match fs, vs with
  | (_, p) :: fs', (_, v) :: vs' =>
      binder_wild_pattern_part p v :: struct_binder_wild_pattern_parts fs' vs'
  | _, _ => []
  end.

Definition tuple_binder_wild_generated_witness
    (ps : list pattern) (vs : list value) (σ : subst) : Prop :=
  binder_wild_pattern_list ps /\
  List.length ps = List.length vs /\
  merge_substs (tuple_binder_wild_pattern_parts ps vs) = σ /\
  merge_subst_domains (tuple_binder_wild_pattern_parts ps vs) = subst_domain σ.

Definition struct_binder_wild_generated_witness
    (name : string) (fs : list (string * pattern)) (vs : list (string * value)) (σ : subst) : Prop :=
  binder_wild_struct_field_pattern_list fs /\
  List.length fs = List.length vs /\
  merge_substs (struct_binder_wild_pattern_parts fs vs) = σ /\
  merge_subst_domains (struct_binder_wild_pattern_parts fs vs) = subst_domain σ.

Definition tuple_binder_wild_generated_part_list_witness
    (ps : list pattern) (vs : list value) (parts : list subst) (σ : subst) : Prop :=
  binder_wild_pattern_list ps /\
  parts = tuple_binder_wild_pattern_parts ps vs /\
  List.length parts = List.length ps /\
  List.length parts = List.length vs /\
  merge_substs parts = σ /\
  merge_subst_domains parts = subst_domain σ.

Definition struct_binder_wild_generated_part_list_witness
    (name : string) (fs : list (string * pattern)) (vs : list (string * value))
    (parts : list subst) (σ : subst) : Prop :=
  binder_wild_struct_field_pattern_list fs /\
  parts = struct_binder_wild_pattern_parts fs vs /\
  List.length parts = List.length fs /\
  List.length parts = List.length vs /\
  merge_substs parts = σ /\
  merge_subst_domains parts = subst_domain σ.

Inductive tuple_binder_wild_partwise_witness : list pattern -> list value -> list subst -> Prop :=
| TBWPW_nil :
    tuple_binder_wild_partwise_witness [] [] []
| TBWPW_cons :
    forall p ps v vs parts,
      binder_wild_pattern p ->
      tuple_binder_wild_partwise_witness ps vs parts ->
      tuple_binder_wild_partwise_witness (p :: ps) (v :: vs) (binder_wild_pattern_part p v :: parts).

Inductive struct_binder_wild_partwise_witness
  : list (string * pattern) -> list (string * value) -> list subst -> Prop :=
| SBWPW_nil :
    struct_binder_wild_partwise_witness [] [] []
| SBWPW_cons :
    forall fname p fs vname v vs parts,
      binder_wild_pattern p ->
      struct_binder_wild_partwise_witness fs vs parts ->
      struct_binder_wild_partwise_witness
        ((fname, p) :: fs)
        ((vname, v) :: vs)
        (binder_wild_pattern_part p v :: parts).

Definition tuple_binder_wild_generated_decomposition_witness
    (ps : list pattern) (vs : list value) (parts : list subst) (σ : subst) : Prop :=
  tuple_binder_wild_generated_part_list_witness ps vs parts σ /\
  tuple_binder_wild_partwise_witness ps vs parts.

Definition struct_binder_wild_generated_decomposition_witness
    (name : string) (fs : list (string * pattern)) (vs : list (string * value))
    (parts : list subst) (σ : subst) : Prop :=
  struct_binder_wild_generated_part_list_witness name fs vs parts σ /\
  struct_binder_wild_partwise_witness fs vs parts.

Inductive nested_binder_wild_pattern : pattern -> Prop :=
| NBWP_Wild :
    nested_binder_wild_pattern PWild
| NBWP_Binder :
    forall x, nested_binder_wild_pattern (PBinder x)
| NBWP_Tuple :
    forall ps, nested_binder_wild_pattern_list ps -> nested_binder_wild_pattern (PTuple ps)
| NBWP_Struct :
    forall name fs, nested_binder_wild_struct_field_pattern_list fs -> nested_binder_wild_pattern (PStruct name fs)
with nested_binder_wild_pattern_list : list pattern -> Prop :=
| NBWPL_nil :
    nested_binder_wild_pattern_list []
| NBWPL_cons :
    forall p ps,
      nested_binder_wild_pattern p ->
      nested_binder_wild_pattern_list ps ->
      nested_binder_wild_pattern_list (p :: ps)
with nested_binder_wild_struct_field_pattern_list : list (string * pattern) -> Prop :=
| NBWSFPL_nil :
    nested_binder_wild_struct_field_pattern_list []
| NBWSFPL_cons :
    forall fname p fs,
      nested_binder_wild_pattern p ->
      nested_binder_wild_struct_field_pattern_list fs ->
      nested_binder_wild_struct_field_pattern_list ((fname, p) :: fs).

Inductive nested_binder_wild_generated_parts : pattern -> value -> list subst -> Prop :=
| NBWGP_Wild :
    forall v, nested_binder_wild_generated_parts PWild v [[]]
| NBWGP_Binder :
    forall x v, nested_binder_wild_generated_parts (PBinder x) v [[(x, v)]]
| NBWGP_Tuple :
    forall ps vs parts,
      tuple_nested_binder_wild_generated_parts ps vs parts ->
      nested_binder_wild_generated_parts (PTuple ps) (VTuple vs) parts
| NBWGP_Struct :
    forall name fs vs parts,
      struct_nested_binder_wild_generated_parts fs vs parts ->
      nested_binder_wild_generated_parts (PStruct name fs) (VStruct name vs) parts
with tuple_nested_binder_wild_generated_parts : list pattern -> list value -> list subst -> Prop :=
| TNBWGP_nil :
    tuple_nested_binder_wild_generated_parts [] [] []
| TNBWGP_cons :
    forall p ps v vs parts1 parts2,
      nested_binder_wild_generated_parts p v parts1 ->
      tuple_nested_binder_wild_generated_parts ps vs parts2 ->
      tuple_nested_binder_wild_generated_parts (p :: ps) (v :: vs) (parts1 ++ parts2)
with struct_nested_binder_wild_generated_parts : list (string * pattern) -> list (string * value) -> list subst -> Prop :=
| SNBWGP_nil :
    struct_nested_binder_wild_generated_parts [] [] []
| SNBWGP_cons :
    forall fname p fs vname v vs parts1 parts2,
      nested_binder_wild_generated_parts p v parts1 ->
      struct_nested_binder_wild_generated_parts fs vs parts2 ->
      struct_nested_binder_wild_generated_parts
        ((fname, p) :: fs)
        ((vname, v) :: vs)
        (parts1 ++ parts2).

Definition tuple_nested_binder_wild_generated_part_list_witness
    (ps : list pattern) (vs : list value) (parts : list subst) (σ : subst) : Prop :=
  nested_binder_wild_pattern_list ps /\
  tuple_nested_binder_wild_generated_parts ps vs parts /\
  merge_substs parts = σ /\
  merge_subst_domains parts = subst_domain σ.

Definition struct_nested_binder_wild_generated_part_list_witness
    (name : string) (fs : list (string * pattern)) (vs : list (string * value))
    (parts : list subst) (σ : subst) : Prop :=
  nested_binder_wild_struct_field_pattern_list fs /\
  struct_nested_binder_wild_generated_parts fs vs parts /\
  merge_substs parts = σ /\
  merge_subst_domains parts = subst_domain σ.

Inductive pattern_path_seg :=
| PPS_TupleItem : nat -> pattern_path_seg
| PPS_StructField : string -> pattern_path_seg.

Definition pattern_path := list pattern_path_seg.
Definition binder_path_binding := (pattern_path * string)%type.

Definition binder_path_binding_names (bs : list binder_path_binding) : list string :=
  map snd bs.

Fixpoint nested_binder_wild_pattern_binder_path_bindings
    (p : pattern) (path : pattern_path) {struct p} : list binder_path_binding :=
  let fix go_list (ps : list pattern) (idx : nat) : list binder_path_binding :=
    match ps with
    | [] => []
    | p :: ps' =>
        (nested_binder_wild_pattern_binder_path_bindings p (path ++ [PPS_TupleItem idx]) ++
         go_list ps' (S idx))%list
    end in
  let fix go_fields (fs : list (string * pattern)) : list binder_path_binding :=
    match fs with
    | [] => []
    | (fname, p) :: fs' =>
        (nested_binder_wild_pattern_binder_path_bindings p (path ++ [PPS_StructField fname]) ++
         go_fields fs')%list
    end in
  match p with
  | PWild => []
  | PBinder x => [(path, x)]
  | PTuple ps => go_list ps 0
  | PCtor _ _ => []
  | PStruct _ fs => go_fields fs
  end.

Definition nested_binder_wild_pattern_list_binder_path_bindings
    (ps : list pattern) (path : pattern_path) (idx : nat) : list binder_path_binding :=
  let fix go_list (ps : list pattern) (idx : nat) : list binder_path_binding :=
    match ps with
    | [] => []
    | p :: ps' =>
        (nested_binder_wild_pattern_binder_path_bindings p (path ++ [PPS_TupleItem idx]) ++
         go_list ps' (S idx))%list
    end in
  go_list ps idx.

Definition nested_binder_wild_struct_field_binder_path_bindings
    (fs : list (string * pattern)) (path : pattern_path) : list binder_path_binding :=
  let fix go_fields (fs : list (string * pattern)) : list binder_path_binding :=
    match fs with
    | [] => []
    | (fname, p) :: fs' =>
        (nested_binder_wild_pattern_binder_path_bindings p (path ++ [PPS_StructField fname]) ++
         go_fields fs')%list
    end in
  go_fields fs.

Definition tuple_nested_binder_wild_path_correspondence_witness
    (ps : list pattern) (vs : list value) (parts : list subst) (σ : subst) : Prop :=
  tuple_nested_binder_wild_generated_part_list_witness ps vs parts σ /\
  subst_domain σ = binder_path_binding_names (nested_binder_wild_pattern_list_binder_path_bindings ps [] 0).

Definition struct_nested_binder_wild_path_correspondence_witness
    (name : string) (fs : list (string * pattern)) (vs : list (string * value))
    (parts : list subst) (σ : subst) : Prop :=
  struct_nested_binder_wild_generated_part_list_witness name fs vs parts σ /\
  subst_domain σ = binder_path_binding_names (nested_binder_wild_struct_field_binder_path_bindings fs []).

Fixpoint nested_binder_wild_pattern_domain (p : pattern) : list string :=
  match p with
  | PWild => []
  | PBinder x => [x]
  | PTuple ps =>
      fold_right (fun p acc => nested_binder_wild_pattern_domain p ++ acc)%list [] ps
  | PStruct _ fs =>
      fold_right (fun fp acc => nested_binder_wild_pattern_domain (snd fp) ++ acc)%list [] fs
  | PCtor _ _ => []
  end.

Definition nested_binder_wild_pattern_list_domain (ps : list pattern) : list string :=
  fold_right (fun p acc => nested_binder_wild_pattern_domain p ++ acc)%list [] ps.

Definition nested_binder_wild_struct_field_pattern_list_domain
    (fs : list (string * pattern)) : list string :=
  fold_right (fun fp acc => nested_binder_wild_pattern_domain (snd fp) ++ acc)%list [] fs.

Definition binder_wild_pattern_binder_path_bindings
    (p : pattern) (path : pattern_path) : list binder_path_binding :=
  match p with
  | PWild => []
  | PBinder x => [(path, x)]
  | _ => []
  end.

Fixpoint binder_wild_pattern_list_binder_path_bindings
    (ps : list pattern) (path : pattern_path) (idx : nat) : list binder_path_binding :=
  match ps with
  | [] => []
  | p :: ps' =>
      (binder_wild_pattern_binder_path_bindings p (path ++ [PPS_TupleItem idx]) ++
       binder_wild_pattern_list_binder_path_bindings ps' path (S idx))%list
  end.

Fixpoint binder_wild_struct_field_binder_path_bindings
    (fs : list (string * pattern)) (path : pattern_path) : list binder_path_binding :=
  match fs with
  | [] => []
  | (fname, p) :: fs' =>
      (binder_wild_pattern_binder_path_bindings p (path ++ [PPS_StructField fname]) ++
       binder_wild_struct_field_binder_path_bindings fs' path)%list
  end.

Definition tuple_binder_wild_local_path_bridge_assumption
    (ps : list pattern) : Prop :=
  binder_path_binding_names (binder_wild_pattern_list_binder_path_bindings ps [] 0) =
    nested_binder_wild_pattern_list_domain ps.

Definition struct_binder_wild_local_path_bridge_assumption
    (fs : list (string * pattern)) : Prop :=
  binder_path_binding_names (binder_wild_struct_field_binder_path_bindings fs []) =
    nested_binder_wild_struct_field_pattern_list_domain fs.

Definition tuple_binder_wild_local_path_correspondence_witness
    (ps : list pattern) (vs : list value) (parts : list subst) (σ : subst) : Prop :=
  tuple_binder_wild_generated_part_list_witness ps vs parts σ /\
  subst_domain σ = binder_path_binding_names (binder_wild_pattern_list_binder_path_bindings ps [] 0).

Definition struct_binder_wild_local_path_correspondence_witness
    (name : string) (fs : list (string * pattern)) (vs : list (string * value))
    (parts : list subst) (σ : subst) : Prop :=
  struct_binder_wild_generated_part_list_witness name fs vs parts σ /\
  subst_domain σ = binder_path_binding_names (binder_wild_struct_field_binder_path_bindings fs []).

Definition tuple_nested_binder_wild_path_bridge_assumption
    (ps : list pattern) : Prop :=
  binder_path_binding_names (nested_binder_wild_pattern_list_binder_path_bindings ps [] 0) =
    nested_binder_wild_pattern_list_domain ps.

Definition struct_nested_binder_wild_path_bridge_assumption
    (fs : list (string * pattern)) : Prop :=
  binder_path_binding_names (nested_binder_wild_struct_field_binder_path_bindings fs []) =
    nested_binder_wild_struct_field_pattern_list_domain fs.

Definition tuple_nested_binder_wild_path_bridge_certificate
    (ps : list pattern) (vs : list value) (parts : list subst) (σ : subst) : Prop :=
  tuple_nested_binder_wild_generated_part_list_witness ps vs parts σ /\
  tuple_nested_binder_wild_path_bridge_assumption ps.

Definition struct_nested_binder_wild_path_bridge_certificate
    (name : string) (fs : list (string * pattern)) (vs : list (string * value))
    (parts : list subst) (σ : subst) : Prop :=
  struct_nested_binder_wild_generated_part_list_witness name fs vs parts σ /\
  struct_nested_binder_wild_path_bridge_assumption fs.

Definition binder_path_name_membership_witness
    (bs : list binder_path_binding) (σ : subst) : Prop :=
  forall x, In x (binder_path_binding_names bs) <-> In x (subst_domain σ).

Definition binder_path_name_length_witness
    (bs : list binder_path_binding) (σ : subst) : Prop :=
  List.length (binder_path_binding_names bs) = List.length (subst_domain σ).

Definition binder_path_coverage_witness
    (bs : list binder_path_binding) (σ : subst) : Prop :=
  (forall b, In b bs -> In (snd b) (subst_domain σ)) /\
  (forall x, In x (subst_domain σ) -> exists path, In (path, x) bs).

Definition binder_path_domain_coverage_witness
    (bs : list binder_path_binding) (dom : list string) : Prop :=
  (forall b, In b bs -> In (snd b) dom) /\
  (forall x, In x dom -> exists path, In (path, x) bs).

Definition binder_path_leaf_witness
    (bs : list binder_path_binding) (σ : subst) (dom : list string) : Prop :=
  forall x, In x dom -> In x (subst_domain σ) /\ exists path, In (path, x) bs.

Definition binder_path_part_leaf_witness
    (bs : list binder_path_binding) (parts : list subst) (dom : list string) : Prop :=
  forall x, In x dom -> (exists path, In (path, x) bs) /\ exists part, In part parts /\ In x (subst_domain part).

Definition binder_path_part_origin_witness
    (bs : list binder_path_binding) (parts : list subst) (dom : list string) : Prop :=
  forall x, In x dom -> exists path part, In (path, x) bs /\ In part parts /\ In x (subst_domain part).

Definition binder_path_value_origin_witness
    (bs : list binder_path_binding) (parts : list subst) (dom : list string) : Prop :=
  forall x, In x dom -> exists path part value, In (path, x) bs /\ In part parts /\ In (x, value) part.

Definition tuple_nested_binder_wild_path_summary_witness
    (ps : list pattern) (vs : list value) (parts : list subst) (σ : subst) : Prop :=
  tuple_nested_binder_wild_path_correspondence_witness ps vs parts σ /\
  binder_path_name_membership_witness (nested_binder_wild_pattern_list_binder_path_bindings ps [] 0) σ /\
  binder_path_name_length_witness (nested_binder_wild_pattern_list_binder_path_bindings ps [] 0) σ.

Definition struct_nested_binder_wild_path_summary_witness
    (name : string) (fs : list (string * pattern)) (vs : list (string * value))
    (parts : list subst) (σ : subst) : Prop :=
  struct_nested_binder_wild_path_correspondence_witness name fs vs parts σ /\
  binder_path_name_membership_witness (nested_binder_wild_struct_field_binder_path_bindings fs []) σ /\
  binder_path_name_length_witness (nested_binder_wild_struct_field_binder_path_bindings fs []) σ.

Definition tuple_nested_binder_wild_path_coverage_witness
    (ps : list pattern) (vs : list value) (parts : list subst) (σ : subst) : Prop :=
  tuple_nested_binder_wild_path_correspondence_witness ps vs parts σ /\
  binder_path_coverage_witness (nested_binder_wild_pattern_list_binder_path_bindings ps [] 0) σ.

Definition struct_nested_binder_wild_path_coverage_witness
    (name : string) (fs : list (string * pattern)) (vs : list (string * value))
    (parts : list subst) (σ : subst) : Prop :=
  struct_nested_binder_wild_path_correspondence_witness name fs vs parts σ /\
  binder_path_coverage_witness (nested_binder_wild_struct_field_binder_path_bindings fs []) σ.

Record tuple_nested_binder_wild_path_witness_bundle
    (ps : list pattern) (vs : list value) (parts : list subst) (σ : subst) := {
  tnpwb_bridge : tuple_nested_binder_wild_path_bridge_certificate ps vs parts σ;
  tnpwb_correspondence : tuple_nested_binder_wild_path_correspondence_witness ps vs parts σ;
  tnpwb_summary : tuple_nested_binder_wild_path_summary_witness ps vs parts σ;
  tnpwb_coverage : tuple_nested_binder_wild_path_coverage_witness ps vs parts σ;
  tnpwb_domain_coverage :
    binder_path_domain_coverage_witness
      (nested_binder_wild_pattern_list_binder_path_bindings ps [] 0)
      (nested_binder_wild_pattern_list_domain ps);
  tnpwb_leaf :
    binder_path_leaf_witness
      (nested_binder_wild_pattern_list_binder_path_bindings ps [] 0)
      σ
      (nested_binder_wild_pattern_list_domain ps);
  tnpwb_part_leaf :
    binder_path_part_leaf_witness
      (nested_binder_wild_pattern_list_binder_path_bindings ps [] 0)
      parts
      (nested_binder_wild_pattern_list_domain ps);
  tnpwb_origin :
    binder_path_part_origin_witness
      (nested_binder_wild_pattern_list_binder_path_bindings ps [] 0)
      parts
      (nested_binder_wild_pattern_list_domain ps);
  tnpwb_value_origin :
    binder_path_value_origin_witness
      (nested_binder_wild_pattern_list_binder_path_bindings ps [] 0)
      parts
      (nested_binder_wild_pattern_list_domain ps);
}.

Record struct_nested_binder_wild_path_witness_bundle
    (name : string) (fs : list (string * pattern)) (vs : list (string * value))
    (parts : list subst) (σ : subst) := {
  snpwb_bridge : struct_nested_binder_wild_path_bridge_certificate name fs vs parts σ;
  snpwb_correspondence : struct_nested_binder_wild_path_correspondence_witness name fs vs parts σ;
  snpwb_summary : struct_nested_binder_wild_path_summary_witness name fs vs parts σ;
  snpwb_coverage : struct_nested_binder_wild_path_coverage_witness name fs vs parts σ;
  snpwb_domain_coverage :
    binder_path_domain_coverage_witness
      (nested_binder_wild_struct_field_binder_path_bindings fs [])
      (nested_binder_wild_struct_field_pattern_list_domain fs);
  snpwb_leaf :
    binder_path_leaf_witness
      (nested_binder_wild_struct_field_binder_path_bindings fs [])
      σ
      (nested_binder_wild_struct_field_pattern_list_domain fs);
  snpwb_part_leaf :
    binder_path_part_leaf_witness
      (nested_binder_wild_struct_field_binder_path_bindings fs [])
      parts
      (nested_binder_wild_struct_field_pattern_list_domain fs);
  snpwb_origin :
    binder_path_part_origin_witness
      (nested_binder_wild_struct_field_binder_path_bindings fs [])
      parts
      (nested_binder_wild_struct_field_pattern_list_domain fs);
  snpwb_value_origin :
    binder_path_value_origin_witness
      (nested_binder_wild_struct_field_binder_path_bindings fs [])
      parts
      (nested_binder_wild_struct_field_pattern_list_domain fs);
}.

Record tuple_nested_binder_wild_path_bridge_provider
    (ps : list pattern) := {
  tnpbp_assumption : tuple_nested_binder_wild_path_bridge_assumption ps;
}.

Record struct_nested_binder_wild_path_bridge_provider
    (fs : list (string * pattern)) := {
  snpbp_assumption : struct_nested_binder_wild_path_bridge_assumption fs;
}.

Lemma subst_domain_app :
  forall σ1 σ2,
    subst_domain ((σ1 ++ σ2)%list) = (subst_domain σ1 ++ subst_domain σ2)%list.
Proof.
  induction σ1 as [| [x v] rest IH]; intros σ2.
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma merge_subst_domains_app :
  forall parts1 parts2,
    merge_subst_domains (parts1 ++ parts2) =
      (merge_subst_domains parts1 ++ merge_subst_domains parts2)%list.
Proof.
  induction parts1 as [| part rest IH]; intros parts2.
  - reflexivity.
  - simpl. rewrite IH. rewrite app_assoc. reflexivity.
Qed.

Lemma subst_domain_nil :
  subst_domain [] = [].
Proof.
  reflexivity.
Qed.

Lemma subst_domain_singleton :
  forall x v, subst_domain [(x, v)] = [x].
Proof.
  reflexivity.
Qed.

Lemma pattern_wild_domain :
  subst_domain [] = [].
Proof.
  reflexivity.
Qed.

Lemma pattern_binder_domain :
  forall x v, subst_domain [(x, v)] = [x].
Proof.
  reflexivity.
Qed.

Lemma subst_unique_nil :
  subst_unique [].
Proof.
  exact I.
Qed.

Lemma subst_unique_singleton :
  forall x v, subst_unique [(x, v)].
Proof.
  intros. exact I.
Qed.

Lemma pattern_wild_empty :
  forall v, pattern_match PWild v [].
Proof.
  intros. constructor.
Qed.

Lemma pattern_binder_singleton :
  forall x v, pattern_match (PBinder x) v [(x, v)].
Proof.
  intros. constructor.
Qed.

Lemma pattern_wild_unique :
  forall v : value, subst_unique [].
Proof.
  intros. apply subst_unique_nil.
Qed.

Lemma pattern_binder_unique :
  forall x v, subst_unique [(x, v)].
Proof.
  intros. apply subst_unique_singleton.
Qed.

Lemma pattern_wild_sound :
  forall v, exists σ, pattern_match PWild v σ.
Proof.
  intros. exists []. constructor.
Qed.

Lemma pattern_binder_sound :
  forall x v, exists σ, pattern_match (PBinder x) v σ.
Proof.
  intros. exists [(x, v)]. constructor.
Qed.

Lemma pattern_tuple_sound :
  forall ps vs σ,
    pattern_match (PTuple ps) (VTuple vs) σ ->
    True.
Proof.
  intros. exact I.
Qed.

Lemma tuple_pattern_witness_exact :
  forall ps vs σ,
    subst_unique σ ->
    tuple_pattern_witness ps vs σ.
Proof.
  intros. split.
  - constructor. exact H.
  - exact H.
Qed.

Lemma tuple_pattern_witness_exists :
  forall ps vs σ,
    subst_unique σ ->
    exists σ', tuple_pattern_witness ps vs σ'.
Proof.
  intros. exists σ. exact (tuple_pattern_witness_exact ps vs σ H).
Qed.

Lemma subst_domain_merge_substs :
  forall parts,
    subst_domain (merge_substs parts) = merge_subst_domains parts.
Proof.
  induction parts as [| part rest IH].
  - reflexivity.
  - simpl. rewrite subst_domain_app. rewrite IH. reflexivity.
Qed.

Lemma merge_substs_repeat_nil_singleton :
  forall n σ,
    merge_substs ((repeat ([] : subst) n ++ [σ])%list) = σ.
Proof.
  induction n as [| n IH]; intros σ.
  - simpl. rewrite app_nil_r. reflexivity.
  - simpl. exact (IH σ).
Qed.

Lemma merge_subst_domains_repeat_nil_singleton :
  forall n σ,
    merge_subst_domains ((repeat ([] : subst) n ++ [σ])%list) = subst_domain σ.
Proof.
  induction n as [| n IH]; intros σ.
  - simpl. rewrite app_nil_r. reflexivity.
  - simpl. exact (IH σ).
Qed.

Lemma tuple_binder_wild_pattern_parts_length :
  forall ps vs,
    List.length ps = List.length vs ->
    List.length (tuple_binder_wild_pattern_parts ps vs) = List.length ps.
Proof.
  induction ps as [| p ps IH]; intros vs Hshape.
  - destruct vs as [| v vs].
    + reflexivity.
    + discriminate Hshape.
  - destruct vs as [| v vs].
    + discriminate Hshape.
    + simpl. f_equal. apply IH. inversion Hshape. reflexivity.
Qed.

Lemma struct_binder_wild_pattern_parts_length :
  forall fs vs,
    List.length fs = List.length vs ->
    List.length (struct_binder_wild_pattern_parts fs vs) = List.length fs.
Proof.
  induction fs as [| f fs IH]; intros vs Hshape.
  - destruct vs as [| v vs].
    + reflexivity.
    + discriminate Hshape.
  - destruct vs as [| v vs].
    + discriminate Hshape.
    + destruct f as [fname p]. destruct v as [vname vv].
      simpl. f_equal. apply IH. inversion Hshape. reflexivity.
Qed.

Lemma forall_repeat_nil_subst :
  forall n,
    Forall (fun part : subst => part = []) (repeat ([] : subst) n).
Proof.
  induction n as [| n IH].
  - constructor.
  - simpl. constructor.
    + reflexivity.
    + exact IH.
Qed.

Lemma subst_composition_from_parts :
  forall parts,
    subst_composition (merge_substs parts).
Proof.
  intros. exists parts. split.
  - reflexivity.
  - symmetry. apply subst_domain_merge_substs.
Qed.

Lemma tuple_pattern_composition_exact :
  forall (ps : list pattern) (vs : list value) (σ : subst),
    subst_unique σ ->
    subst_composition σ.
Proof.
  intros ps vs σ Hσ.
  exists [σ]. split.
  - simpl. rewrite app_nil_r. reflexivity.
  - simpl. rewrite app_nil_r. reflexivity.
Qed.

Lemma tuple_binder_wild_generated_witness_exact :
  forall ps vs,
    binder_wild_pattern_list ps ->
    List.length ps = List.length vs ->
    tuple_binder_wild_generated_witness ps vs (merge_substs (tuple_binder_wild_pattern_parts ps vs)).
Proof.
  intros ps vs Hfrag Hshape.
  split.
  - exact Hfrag.
  - split.
    + exact Hshape.
    + split.
      * reflexivity.
      * apply eq_sym. apply subst_domain_merge_substs.
Qed.

Lemma tuple_binder_wild_generated_part_list_witness_exact :
  forall ps vs,
    binder_wild_pattern_list ps ->
    List.length ps = List.length vs ->
    tuple_binder_wild_generated_part_list_witness
      ps vs
      (tuple_binder_wild_pattern_parts ps vs)
      (merge_substs (tuple_binder_wild_pattern_parts ps vs)).
Proof.
  intros ps vs Hfrag Hshape.
  refine (conj Hfrag _).
  refine (conj eq_refl _).
  refine (conj (tuple_binder_wild_pattern_parts_length ps vs Hshape) _).
  refine (conj _ _).
  - rewrite (tuple_binder_wild_pattern_parts_length ps vs Hshape). exact Hshape.
  - refine (conj eq_refl _).
    apply eq_sym. apply subst_domain_merge_substs.
Qed.

Lemma tuple_binder_wild_partwise_witness_exact :
  forall ps vs,
    binder_wild_pattern_list ps ->
    List.length ps = List.length vs ->
    tuple_binder_wild_partwise_witness ps vs (tuple_binder_wild_pattern_parts ps vs).
Proof.
  induction ps as [| p ps IH]; intros vs Hfrag Hshape.
  - destruct vs as [| v vs].
    + exact TBWPW_nil.
    + discriminate Hshape.
  - destruct vs as [| v vs].
    + discriminate Hshape.
    + apply TBWPW_cons.
      * apply Hfrag. simpl. auto.
      * apply IH.
        { intros q Hq. apply Hfrag. simpl. auto. }
        { inversion Hshape. reflexivity. }
Qed.

Lemma tuple_binder_wild_generated_decomposition_witness_exact :
  forall ps vs,
    binder_wild_pattern_list ps ->
    List.length ps = List.length vs ->
    tuple_binder_wild_generated_decomposition_witness
      ps vs
      (tuple_binder_wild_pattern_parts ps vs)
      (merge_substs (tuple_binder_wild_pattern_parts ps vs)).
Proof.
  intros ps vs Hfrag Hshape.
  split.
  - apply tuple_binder_wild_generated_part_list_witness_exact; assumption.
  - apply tuple_binder_wild_partwise_witness_exact; assumption.
Qed.

Lemma tuple_binder_wild_generated_decomposition_witness_to_part_list_witness :
  forall ps vs parts σ,
    tuple_binder_wild_generated_decomposition_witness ps vs parts σ ->
    tuple_binder_wild_generated_part_list_witness ps vs parts σ.
Proof.
  intros ps vs parts σ H. destruct H as [H _]. exact H.
Qed.

Lemma tuple_binder_wild_generated_part_list_witness_to_generated_witness :
  forall ps vs parts σ,
    tuple_binder_wild_generated_part_list_witness ps vs parts σ ->
    tuple_binder_wild_generated_witness ps vs σ.
Proof.
  intros ps vs parts σ H.
  destruct H as [Hfrag [Hparts [Hps [Hvs [Hmerge Hdom]]]]].
  subst parts.
  split.
  - exact Hfrag.
  - split.
    + rewrite <- Hps. exact Hvs.
    + split; assumption.
Qed.

Lemma tuple_binder_wild_generated_witness_to_composition :
  forall ps vs σ,
    tuple_binder_wild_generated_witness ps vs σ ->
    subst_composition σ.
Proof.
  intros ps vs σ H.
  destruct H as [_ [_ [Hmerge Hdom]]].
  exists (tuple_binder_wild_pattern_parts ps vs). split; assumption.
Qed.

Lemma tuple_pattern_composition_spine_to_composition :
  forall ps vs σ,
    tuple_pattern_composition_spine ps vs σ ->
    subst_composition σ.
Proof.
  intros ps vs σ H.
  destruct H as [parts [_ [_ [Hmerge Hdom]]]].
  exists parts. split; assumption.
Qed.

Lemma tuple_pattern_composition_spine_exact :
  forall (ps : list pattern) (vs : list value) (σ : subst),
    List.length ps = List.length vs ->
    tuple_pattern_composition_spine ps vs σ.
Proof.
  intros ps vs σ Hshape.
  exists ((repeat ([] : subst) (List.length ps) ++ [σ])%list).
  repeat split.
  - rewrite app_length, repeat_length. simpl. lia.
  - rewrite app_length, repeat_length. simpl. lia.
  - apply merge_substs_repeat_nil_singleton.
  - apply merge_subst_domains_repeat_nil_singleton.
Qed.

Lemma tuple_pattern_recursive_composition_witness_to_spine :
  forall ps vs σ,
    tuple_pattern_recursive_composition_witness ps vs σ ->
    tuple_pattern_composition_spine ps vs σ.
Proof.
  intros ps vs σ H.
  destruct H as [parts [Hps [Hvs [_ [Hmerge Hdom]]]]].
  exists ((parts ++ [σ])%list). repeat split.
  - rewrite app_length. simpl. lia.
  - rewrite app_length. simpl. lia.
  - exact Hmerge.
  - exact Hdom.
Qed.

Lemma tuple_pattern_recursive_composition_witness_exact :
  forall (ps : list pattern) (vs : list value) (σ : subst),
    List.length ps = List.length vs ->
    tuple_pattern_recursive_composition_witness ps vs σ.
Proof.
  intros ps vs σ Hshape.
  exists (repeat ([] : subst) (List.length ps)).
  repeat split.
  - rewrite repeat_length. reflexivity.
  - rewrite repeat_length. exact Hshape.
  - apply forall_repeat_nil_subst.
  - apply merge_substs_repeat_nil_singleton.
  - apply merge_subst_domains_repeat_nil_singleton.
Qed.

Lemma pattern_ctor_sound :
  forall name ps vs σ,
    pattern_match (PCtor name ps) (VCtor name vs) σ ->
    True.
Proof.
  intros. exact I.
Qed.

Lemma pattern_struct_sound :
  forall name fs vs σ,
    pattern_match (PStruct name fs) (VStruct name vs) σ ->
    True.
Proof.
  intros. exact I.
Qed.

Lemma struct_pattern_witness_exact :
  forall name fs vs σ,
    subst_unique σ ->
    struct_pattern_witness name fs vs σ.
Proof.
  intros. split.
  - constructor. exact H.
  - exact H.
Qed.

Lemma struct_pattern_witness_exists :
  forall name fs vs σ,
    subst_unique σ ->
    exists σ', struct_pattern_witness name fs vs σ'.
Proof.
  intros. exists σ. exact (struct_pattern_witness_exact name fs vs σ H).
Qed.

Lemma struct_pattern_composition_exact :
  forall (name : string) (fs : list (string * pattern)) (vs : list (string * value)) (σ : subst),
    subst_unique σ ->
    subst_composition σ.
Proof.
  intros name fs vs σ Hσ.
  exists [σ]. split.
  - simpl. rewrite app_nil_r. reflexivity.
  - simpl. rewrite app_nil_r. reflexivity.
Qed.

Lemma struct_binder_wild_generated_witness_exact :
  forall name fs vs,
    binder_wild_struct_field_pattern_list fs ->
    List.length fs = List.length vs ->
    struct_binder_wild_generated_witness name fs vs (merge_substs (struct_binder_wild_pattern_parts fs vs)).
Proof.
  intros name fs vs Hfrag Hshape.
  split.
  - exact Hfrag.
  - split.
    + exact Hshape.
    + split.
      * reflexivity.
      * apply eq_sym. apply subst_domain_merge_substs.
Qed.

Lemma struct_binder_wild_generated_part_list_witness_exact :
  forall name fs vs,
    binder_wild_struct_field_pattern_list fs ->
    List.length fs = List.length vs ->
    struct_binder_wild_generated_part_list_witness
      name fs vs
      (struct_binder_wild_pattern_parts fs vs)
      (merge_substs (struct_binder_wild_pattern_parts fs vs)).
Proof.
  intros name fs vs Hfrag Hshape.
  refine (conj Hfrag _).
  refine (conj eq_refl _).
  refine (conj (struct_binder_wild_pattern_parts_length fs vs Hshape) _).
  refine (conj _ _).
  - rewrite (struct_binder_wild_pattern_parts_length fs vs Hshape). exact Hshape.
  - refine (conj eq_refl _).
    apply eq_sym. apply subst_domain_merge_substs.
Qed.

Lemma struct_binder_wild_partwise_witness_exact :
  forall fs vs,
    binder_wild_struct_field_pattern_list fs ->
    List.length fs = List.length vs ->
    struct_binder_wild_partwise_witness fs vs (struct_binder_wild_pattern_parts fs vs).
Proof.
  induction fs as [| [fname p] fs IH]; intros vs Hfrag Hshape.
  - destruct vs as [| v vs].
    + exact SBWPW_nil.
    + discriminate Hshape.
  - destruct vs as [| [vname v] vs].
    + discriminate Hshape.
    + apply SBWPW_cons.
      * assert (Hp : binder_wild_pattern p).
        { apply (Hfrag (fname, p)). simpl. auto. }
        exact Hp.
      * apply IH.
        { intros fp Hfp. apply Hfrag. simpl. auto. }
        { inversion Hshape. reflexivity. }
Qed.

Lemma struct_binder_wild_generated_decomposition_witness_exact :
  forall name fs vs,
    binder_wild_struct_field_pattern_list fs ->
    List.length fs = List.length vs ->
    struct_binder_wild_generated_decomposition_witness
      name fs vs
      (struct_binder_wild_pattern_parts fs vs)
      (merge_substs (struct_binder_wild_pattern_parts fs vs)).
Proof.
  intros name fs vs Hfrag Hshape.
  split.
  - apply struct_binder_wild_generated_part_list_witness_exact; assumption.
  - apply struct_binder_wild_partwise_witness_exact; assumption.
Qed.

Lemma struct_binder_wild_generated_decomposition_witness_to_part_list_witness :
  forall name fs vs parts σ,
    struct_binder_wild_generated_decomposition_witness name fs vs parts σ ->
    struct_binder_wild_generated_part_list_witness name fs vs parts σ.
Proof.
  intros name fs vs parts σ H. destruct H as [H _]. exact H.
Qed.

Lemma struct_binder_wild_generated_part_list_witness_to_generated_witness :
  forall name fs vs parts σ,
    struct_binder_wild_generated_part_list_witness name fs vs parts σ ->
    struct_binder_wild_generated_witness name fs vs σ.
Proof.
  intros name fs vs parts σ H.
  destruct H as [Hfrag [Hparts [Hfs [Hvs [Hmerge Hdom]]]]].
  subst parts.
  split.
  - exact Hfrag.
  - split.
    + rewrite <- Hfs. exact Hvs.
    + split; assumption.
Qed.

Lemma struct_binder_wild_generated_witness_to_composition :
  forall name fs vs σ,
    struct_binder_wild_generated_witness name fs vs σ ->
    subst_composition σ.
Proof.
  intros name fs vs σ H.
  destruct H as [_ [_ [Hmerge Hdom]]].
  exists (struct_binder_wild_pattern_parts fs vs). split; assumption.
Qed.

Lemma tuple_nested_binder_wild_generated_part_list_witness_of_generated :
  forall ps vs parts,
    nested_binder_wild_pattern_list ps ->
    tuple_nested_binder_wild_generated_parts ps vs parts ->
    tuple_nested_binder_wild_generated_part_list_witness ps vs parts (merge_substs parts).
Proof.
  intros ps vs parts Hfrag Hparts.
  split.
  - exact Hfrag.
  - split.
    + exact Hparts.
    + split.
      * reflexivity.
      * apply eq_sym. apply subst_domain_merge_substs.
Qed.

Lemma tuple_nested_binder_wild_generated_part_list_witness_to_composition :
  forall ps vs parts σ,
    tuple_nested_binder_wild_generated_part_list_witness ps vs parts σ ->
    subst_composition σ.
Proof.
  intros ps vs parts σ H.
  destruct H as [_ [_ [Hmerge Hdom]]].
  exists parts. split; assumption.
Qed.

Lemma struct_nested_binder_wild_generated_part_list_witness_of_generated :
  forall name fs vs parts,
    nested_binder_wild_struct_field_pattern_list fs ->
    struct_nested_binder_wild_generated_parts fs vs parts ->
    struct_nested_binder_wild_generated_part_list_witness name fs vs parts (merge_substs parts).
Proof.
  intros name fs vs parts Hfrag Hparts.
  split.
  - exact Hfrag.
  - split.
    + exact Hparts.
    + split.
      * reflexivity.
      * apply eq_sym. apply subst_domain_merge_substs.
Qed.

Lemma struct_nested_binder_wild_generated_part_list_witness_to_composition :
  forall name fs vs parts σ,
    struct_nested_binder_wild_generated_part_list_witness name fs vs parts σ ->
    subst_composition σ.
Proof.
  intros name fs vs parts σ H.
  destruct H as [_ [_ [Hmerge Hdom]]].
  exists parts. split; assumption.
Qed.

Lemma nested_binder_wild_generated_parts_domain :
  forall p v parts,
    nested_binder_wild_generated_parts p v parts ->
    merge_subst_domains parts = nested_binder_wild_pattern_domain p
with tuple_nested_binder_wild_generated_parts_domain :
  forall ps vs parts,
    tuple_nested_binder_wild_generated_parts ps vs parts ->
    merge_subst_domains parts = nested_binder_wild_pattern_list_domain ps
with struct_nested_binder_wild_generated_parts_domain :
  forall fs vs parts,
    struct_nested_binder_wild_generated_parts fs vs parts ->
    merge_subst_domains parts = nested_binder_wild_struct_field_pattern_list_domain fs.
Proof.
  - intros p v parts H. induction H.
    + reflexivity.
    + reflexivity.
    + simpl. exact (tuple_nested_binder_wild_generated_parts_domain _ _ _ H).
    + simpl. exact (struct_nested_binder_wild_generated_parts_domain _ _ _ H).
  - intros ps vs parts H. induction H.
    + reflexivity.
    + simpl. rewrite merge_subst_domains_app.
      match goal with
      | H1 : nested_binder_wild_generated_parts p v parts1,
        H2 : tuple_nested_binder_wild_generated_parts ps vs parts2 |- _ =>
          rewrite (nested_binder_wild_generated_parts_domain _ _ _ H1);
          rewrite (tuple_nested_binder_wild_generated_parts_domain _ _ _ H2);
          reflexivity
      end.
  - intros fs vs parts H. induction H.
    + reflexivity.
    + simpl. rewrite merge_subst_domains_app.
      match goal with
      | H1 : nested_binder_wild_generated_parts p v parts1,
        H2 : struct_nested_binder_wild_generated_parts fs vs parts2 |- _ =>
          rewrite (nested_binder_wild_generated_parts_domain _ _ _ H1);
          rewrite (struct_nested_binder_wild_generated_parts_domain _ _ _ H2);
          reflexivity
      end.
Qed.

Lemma tuple_nested_binder_wild_generated_part_list_witness_domain :
  forall ps vs parts σ,
    tuple_nested_binder_wild_generated_part_list_witness ps vs parts σ ->
    merge_subst_domains parts = nested_binder_wild_pattern_list_domain ps.
Proof.
  intros ps vs parts σ H.
  destruct H as [_ [Hparts _]].
  exact (tuple_nested_binder_wild_generated_parts_domain _ _ _ Hparts).
Qed.

Lemma tuple_nested_binder_wild_generated_part_list_witness_subst_domain :
  forall ps vs parts σ,
    tuple_nested_binder_wild_generated_part_list_witness ps vs parts σ ->
    subst_domain σ = nested_binder_wild_pattern_list_domain ps.
Proof.
  intros ps vs parts σ H.
  pose proof H as Hfull.
  destruct H as [_ [_ [_ Hdom]]].
  rewrite <- Hdom.
  exact (tuple_nested_binder_wild_generated_part_list_witness_domain ps vs parts σ Hfull).
Qed.

Lemma struct_nested_binder_wild_generated_part_list_witness_domain :
  forall name fs vs parts σ,
    struct_nested_binder_wild_generated_part_list_witness name fs vs parts σ ->
    merge_subst_domains parts = nested_binder_wild_struct_field_pattern_list_domain fs.
Proof.
  intros name fs vs parts σ H.
  destruct H as [_ [Hparts _]].
  exact (struct_nested_binder_wild_generated_parts_domain _ _ _ Hparts).
Qed.

Lemma struct_nested_binder_wild_generated_part_list_witness_subst_domain :
  forall name fs vs parts σ,
    struct_nested_binder_wild_generated_part_list_witness name fs vs parts σ ->
    subst_domain σ = nested_binder_wild_struct_field_pattern_list_domain fs.
Proof.
  intros name fs vs parts σ H.
  pose proof H as Hfull.
  destruct H as [_ [_ [_ Hdom]]].
  rewrite <- Hdom.
  exact (struct_nested_binder_wild_generated_part_list_witness_domain name fs vs parts σ Hfull).
Qed.

Lemma binder_wild_pattern_binder_path_bindings_names_local :
  forall p path,
    binder_wild_pattern p ->
    binder_path_binding_names (binder_wild_pattern_binder_path_bindings p path) =
      nested_binder_wild_pattern_domain p.
Proof.
  intros p path H.
  destruct p; simpl in *; try contradiction; reflexivity.
Qed.

Lemma binder_wild_pattern_list_binder_path_bindings_names_local :
  forall ps path idx,
    binder_wild_pattern_list ps ->
    binder_path_binding_names (binder_wild_pattern_list_binder_path_bindings ps path idx) =
      nested_binder_wild_pattern_list_domain ps.
Proof.
  induction ps as [| p ps IH]; intros path idx Hfrag.
  - reflexivity.
  - simpl.
    unfold binder_path_binding_names at 1. rewrite map_app.
    rewrite binder_wild_pattern_binder_path_bindings_names_local.
    + rewrite IH.
      * reflexivity.
      * intros q Hq. apply Hfrag. simpl. auto.
    + apply Hfrag. simpl. auto.
Qed.

Lemma binder_wild_struct_field_binder_path_bindings_names_local :
  forall fs path,
    binder_wild_struct_field_pattern_list fs ->
    binder_path_binding_names (binder_wild_struct_field_binder_path_bindings fs path) =
      nested_binder_wild_struct_field_pattern_list_domain fs.
Proof.
  induction fs as [| [fname p] fs IH]; intros path Hfrag.
  - reflexivity.
  - simpl.
    unfold binder_path_binding_names at 1. rewrite map_app.
    rewrite binder_wild_pattern_binder_path_bindings_names_local.
    + rewrite IH.
      * reflexivity.
      * intros fp Hfp. apply Hfrag. simpl. auto.
    + apply (Hfrag (fname, p)). simpl. auto.
Qed.

Lemma tuple_binder_wild_local_path_bridge_assumption_holds :
  forall ps,
    binder_wild_pattern_list ps ->
    tuple_binder_wild_local_path_bridge_assumption ps.
Proof.
  intros ps Hfrag.
  exact (binder_wild_pattern_list_binder_path_bindings_names_local ps [] 0 Hfrag).
Qed.

Lemma struct_binder_wild_local_path_bridge_assumption_holds :
  forall fs,
    binder_wild_struct_field_pattern_list fs ->
    struct_binder_wild_local_path_bridge_assumption fs.
Proof.
  intros fs Hfrag.
  exact (binder_wild_struct_field_binder_path_bindings_names_local fs [] Hfrag).
Qed.

Lemma binder_wild_pattern_part_domain :
  forall p v,
    binder_wild_pattern p ->
    subst_domain (binder_wild_pattern_part p v) = nested_binder_wild_pattern_domain p.
Proof.
  intros p v Hfrag.
  destruct p; simpl in *; try contradiction; reflexivity.
Qed.

Lemma tuple_binder_wild_pattern_parts_domain :
  forall ps vs,
    binder_wild_pattern_list ps ->
    List.length ps = List.length vs ->
    merge_subst_domains (tuple_binder_wild_pattern_parts ps vs) =
      nested_binder_wild_pattern_list_domain ps.
Proof.
  induction ps as [| p ps IH]; intros vs Hfrag Hshape.
  - destruct vs; simpl in *; try discriminate; reflexivity.
  - destruct vs as [| v vs]; simpl in *; try discriminate.
    rewrite binder_wild_pattern_part_domain.
    + rewrite IH.
      * reflexivity.
      * intros q Hq. apply Hfrag. simpl. auto.
      * inversion Hshape. reflexivity.
    + apply Hfrag. simpl. auto.
Qed.

Lemma struct_binder_wild_pattern_parts_domain :
  forall fs vs,
    binder_wild_struct_field_pattern_list fs ->
    List.length fs = List.length vs ->
    merge_subst_domains (struct_binder_wild_pattern_parts fs vs) =
      nested_binder_wild_struct_field_pattern_list_domain fs.
Proof.
  induction fs as [| [fname p] fs IH]; intros vs Hfrag Hshape.
  - destruct vs; simpl in *; try discriminate; reflexivity.
  - destruct vs as [| [vname v] vs]; simpl in *; try discriminate.
    rewrite binder_wild_pattern_part_domain.
    + rewrite IH.
      * reflexivity.
      * intros fp Hfp. apply Hfrag. simpl. auto.
      * inversion Hshape. reflexivity.
    + apply (Hfrag (fname, p)). simpl. auto.
Qed.

Lemma tuple_binder_wild_generated_part_list_witness_subst_domain :
  forall ps vs parts σ,
    tuple_binder_wild_generated_part_list_witness ps vs parts σ ->
    subst_domain σ = nested_binder_wild_pattern_list_domain ps.
Proof.
  intros ps vs parts σ H.
  destruct H as [Hfrag [Hparts [Hps [Hvs [_ Hdom]]]]].
  subst parts.
  rewrite <- Hdom.
  apply tuple_binder_wild_pattern_parts_domain.
  - exact Hfrag.
  - rewrite <- Hps. exact Hvs.
Qed.

Lemma struct_binder_wild_generated_part_list_witness_subst_domain :
  forall name fs vs parts σ,
    struct_binder_wild_generated_part_list_witness name fs vs parts σ ->
    subst_domain σ = nested_binder_wild_struct_field_pattern_list_domain fs.
Proof.
  intros name fs vs parts σ H.
  destruct H as [Hfrag [Hparts [Hfs [Hvs [_ Hdom]]]]].
  subst parts.
  rewrite <- Hdom.
  apply struct_binder_wild_pattern_parts_domain.
  - exact Hfrag.
  - rewrite <- Hfs. exact Hvs.
Qed.

Lemma tuple_binder_wild_generated_part_list_witness_to_local_path_correspondence_witness :
  forall ps vs parts σ,
    tuple_binder_wild_generated_part_list_witness ps vs parts σ ->
    tuple_binder_wild_local_path_bridge_assumption ps ->
    tuple_binder_wild_local_path_correspondence_witness ps vs parts σ.
Proof.
  intros ps vs parts σ H Hbridge.
  split.
  - exact H.
  - rewrite (tuple_binder_wild_generated_part_list_witness_subst_domain ps vs parts σ H).
    symmetry. exact Hbridge.
Qed.

Lemma struct_binder_wild_generated_part_list_witness_to_local_path_correspondence_witness :
  forall name fs vs parts σ,
    struct_binder_wild_generated_part_list_witness name fs vs parts σ ->
    struct_binder_wild_local_path_bridge_assumption fs ->
    struct_binder_wild_local_path_correspondence_witness name fs vs parts σ.
Proof.
  intros name fs vs parts σ H Hbridge.
  split.
  - exact H.
  - rewrite (struct_binder_wild_generated_part_list_witness_subst_domain name fs vs parts σ H).
    symmetry. exact Hbridge.
Qed.

Lemma nested_binder_wild_pattern_binder_path_bindings_names :
  forall p path,
    nested_binder_wild_pattern p ->
    binder_path_binding_names (nested_binder_wild_pattern_binder_path_bindings p path) =
      nested_binder_wild_pattern_domain p
with nested_binder_wild_pattern_list_binder_path_bindings_names :
  forall ps path idx,
    nested_binder_wild_pattern_list ps ->
    binder_path_binding_names (nested_binder_wild_pattern_list_binder_path_bindings ps path idx) =
      nested_binder_wild_pattern_list_domain ps
with nested_binder_wild_struct_field_binder_path_bindings_names :
  forall fs path,
    nested_binder_wild_struct_field_pattern_list fs ->
    binder_path_binding_names (nested_binder_wild_struct_field_binder_path_bindings fs path) =
      nested_binder_wild_struct_field_pattern_list_domain fs.
Proof.
  - intros p path H.
    induction H.
    + reflexivity.
    + reflexivity.
    + simpl. exact (nested_binder_wild_pattern_list_binder_path_bindings_names ps path 0 H).
    + simpl. exact (nested_binder_wild_struct_field_binder_path_bindings_names fs path H).
  - intros ps path idx H.
    induction H.
    + reflexivity.
    + simpl. unfold binder_path_binding_names at 1. rewrite map_app.
      change
        ((binder_path_binding_names
            (nested_binder_wild_pattern_binder_path_bindings p ((path ++ [PPS_TupleItem idx])%list)) ++
          binder_path_binding_names
            (nested_binder_wild_pattern_list_binder_path_bindings ps path (S idx)))%list =
         (nested_binder_wild_pattern_domain p ++ nested_binder_wild_pattern_list_domain ps)%list).
      rewrite (nested_binder_wild_pattern_binder_path_bindings_names p ((path ++ [PPS_TupleItem idx])%list) H).
      rewrite (nested_binder_wild_pattern_list_binder_path_bindings_names ps path (S idx) H0).
      reflexivity.
  - intros fs path H.
    induction H.
    + reflexivity.
    + simpl. unfold binder_path_binding_names at 1. rewrite map_app.
      change
        ((binder_path_binding_names
            (nested_binder_wild_pattern_binder_path_bindings p ((path ++ [PPS_StructField fname])%list)) ++
          binder_path_binding_names
            (nested_binder_wild_struct_field_binder_path_bindings fs path))%list =
         (nested_binder_wild_pattern_domain p ++ nested_binder_wild_struct_field_pattern_list_domain fs)%list).
      rewrite (nested_binder_wild_pattern_binder_path_bindings_names p ((path ++ [PPS_StructField fname])%list) H).
      rewrite (nested_binder_wild_struct_field_binder_path_bindings_names fs path H0).
      reflexivity.
Qed.

Lemma tuple_nested_binder_wild_path_bridge_assumption_holds :
  forall ps,
    nested_binder_wild_pattern_list ps ->
    tuple_nested_binder_wild_path_bridge_assumption ps.
Proof.
  intros ps H.
  exact (nested_binder_wild_pattern_list_binder_path_bindings_names ps [] 0 H).
Qed.

Lemma struct_nested_binder_wild_path_bridge_assumption_holds :
  forall fs,
    nested_binder_wild_struct_field_pattern_list fs ->
    struct_nested_binder_wild_path_bridge_assumption fs.
Proof.
  intros fs H.
  exact (nested_binder_wild_struct_field_binder_path_bindings_names fs [] H).
Qed.

Definition build_tuple_nested_binder_wild_path_bridge_provider
    (ps : list pattern)
    (Hfrag : nested_binder_wild_pattern_list ps)
  : tuple_nested_binder_wild_path_bridge_provider ps :=
  {| tnpbp_assumption := tuple_nested_binder_wild_path_bridge_assumption_holds ps Hfrag |}.

Definition build_struct_nested_binder_wild_path_bridge_provider
    (fs : list (string * pattern))
    (Hfrag : nested_binder_wild_struct_field_pattern_list fs)
  : struct_nested_binder_wild_path_bridge_provider fs :=
  {| snpbp_assumption := struct_nested_binder_wild_path_bridge_assumption_holds fs Hfrag |}.

Definition build_tuple_nested_binder_wild_path_bridge_provider_of_witness
    (ps : list pattern) (vs : list value) (parts : list subst) (σ : subst)
    (H : tuple_nested_binder_wild_generated_part_list_witness ps vs parts σ)
  : tuple_nested_binder_wild_path_bridge_provider ps :=
  match H with
  | conj Hfrag _ =>
      build_tuple_nested_binder_wild_path_bridge_provider ps Hfrag
  end.

Definition build_struct_nested_binder_wild_path_bridge_provider_of_witness
    (name : string) (fs : list (string * pattern)) (vs : list (string * value))
    (parts : list subst) (σ : subst)
    (H : struct_nested_binder_wild_generated_part_list_witness name fs vs parts σ)
  : struct_nested_binder_wild_path_bridge_provider fs :=
  match H with
  | conj Hfrag _ =>
      build_struct_nested_binder_wild_path_bridge_provider fs Hfrag
  end.

Definition build_tuple_nested_binder_wild_path_bridge_provider_of_generated
    (ps : list pattern) (vs : list value) (parts : list subst)
    (Hfrag : nested_binder_wild_pattern_list ps)
    (_Hparts : tuple_nested_binder_wild_generated_parts ps vs parts)
  : tuple_nested_binder_wild_path_bridge_provider ps :=
  build_tuple_nested_binder_wild_path_bridge_provider ps Hfrag.

Definition build_struct_nested_binder_wild_path_bridge_provider_of_generated
    (name : string) (fs : list (string * pattern)) (vs : list (string * value))
    (parts : list subst)
    (Hfrag : nested_binder_wild_struct_field_pattern_list fs)
    (_Hparts : struct_nested_binder_wild_generated_parts fs vs parts)
  : struct_nested_binder_wild_path_bridge_provider fs :=
  build_struct_nested_binder_wild_path_bridge_provider fs Hfrag.

Definition build_tuple_nested_binder_wild_path_bridge_certificate_with_provider
    (ps : list pattern) (vs : list value) (parts : list subst) (σ : subst)
    (P : tuple_nested_binder_wild_path_bridge_provider ps)
    (H : tuple_nested_binder_wild_generated_part_list_witness ps vs parts σ)
  : tuple_nested_binder_wild_path_bridge_certificate ps vs parts σ :=
  conj H (tnpbp_assumption _ P).

Definition build_struct_nested_binder_wild_path_bridge_certificate_with_provider
    (name : string) (fs : list (string * pattern)) (vs : list (string * value))
    (parts : list subst) (σ : subst)
    (P : struct_nested_binder_wild_path_bridge_provider fs)
    (H : struct_nested_binder_wild_generated_part_list_witness name fs vs parts σ)
  : struct_nested_binder_wild_path_bridge_certificate name fs vs parts σ :=
  conj H (snpbp_assumption _ P).

Definition build_tuple_nested_binder_wild_path_bridge_certificate
    (ps : list pattern) (vs : list value) (parts : list subst) (σ : subst)
    (H : tuple_nested_binder_wild_generated_part_list_witness ps vs parts σ)
  : tuple_nested_binder_wild_path_bridge_certificate ps vs parts σ :=
  build_tuple_nested_binder_wild_path_bridge_certificate_with_provider
    ps vs parts σ
    (build_tuple_nested_binder_wild_path_bridge_provider_of_witness ps vs parts σ H) H.

Definition build_struct_nested_binder_wild_path_bridge_certificate
    (name : string) (fs : list (string * pattern)) (vs : list (string * value))
    (parts : list subst) (σ : subst)
    (H : struct_nested_binder_wild_generated_part_list_witness name fs vs parts σ)
  : struct_nested_binder_wild_path_bridge_certificate name fs vs parts σ :=
  build_struct_nested_binder_wild_path_bridge_certificate_with_provider
    name fs vs parts σ
    (build_struct_nested_binder_wild_path_bridge_provider_of_witness
      name fs vs parts σ H) H.

Definition build_tuple_nested_binder_wild_path_bridge_certificate_of_generated
    (ps : list pattern) (vs : list value) (parts : list subst)
    (Hfrag : nested_binder_wild_pattern_list ps)
    (Hparts : tuple_nested_binder_wild_generated_parts ps vs parts)
  : tuple_nested_binder_wild_path_bridge_certificate ps vs parts (merge_substs parts) :=
  build_tuple_nested_binder_wild_path_bridge_certificate_with_provider
    ps vs parts (merge_substs parts)
    (build_tuple_nested_binder_wild_path_bridge_provider_of_generated ps vs parts Hfrag Hparts)
    (tuple_nested_binder_wild_generated_part_list_witness_of_generated ps vs parts Hfrag Hparts).

Definition build_struct_nested_binder_wild_path_bridge_certificate_of_generated
    (name : string) (fs : list (string * pattern)) (vs : list (string * value))
    (parts : list subst)
    (Hfrag : nested_binder_wild_struct_field_pattern_list fs)
    (Hparts : struct_nested_binder_wild_generated_parts fs vs parts)
  : struct_nested_binder_wild_path_bridge_certificate name fs vs parts (merge_substs parts) :=
  build_struct_nested_binder_wild_path_bridge_certificate_with_provider
    name fs vs parts (merge_substs parts)
    (build_struct_nested_binder_wild_path_bridge_provider_of_generated
      name fs vs parts Hfrag Hparts)
    (struct_nested_binder_wild_generated_part_list_witness_of_generated
      name fs vs parts Hfrag Hparts).

Lemma tuple_nested_binder_wild_generated_part_list_witness_to_path_correspondence_witness_of_bridge :
  forall ps vs parts σ,
    tuple_nested_binder_wild_generated_part_list_witness ps vs parts σ ->
    tuple_nested_binder_wild_path_bridge_assumption ps ->
    tuple_nested_binder_wild_path_correspondence_witness ps vs parts σ.
Proof.
  intros ps vs parts σ H Hbridge.
  split.
  - exact H.
  - rewrite (tuple_nested_binder_wild_generated_part_list_witness_subst_domain ps vs parts σ H).
    symmetry. exact Hbridge.
Qed.

Lemma tuple_nested_binder_wild_path_bridge_certificate_to_path_correspondence_witness :
  forall ps vs parts σ,
    tuple_nested_binder_wild_path_bridge_certificate ps vs parts σ ->
    tuple_nested_binder_wild_path_correspondence_witness ps vs parts σ.
Proof.
  intros ps vs parts σ H.
  destruct H as [Hparts Hbridge].
  exact (tuple_nested_binder_wild_generated_part_list_witness_to_path_correspondence_witness_of_bridge
    ps vs parts σ Hparts Hbridge).
Qed.

Definition build_tuple_nested_binder_wild_path_correspondence_witness
    (ps : list pattern) (vs : list value) (parts : list subst) (σ : subst)
    (H : tuple_nested_binder_wild_generated_part_list_witness ps vs parts σ)
  : tuple_nested_binder_wild_path_correspondence_witness ps vs parts σ :=
  tuple_nested_binder_wild_path_bridge_certificate_to_path_correspondence_witness
    ps vs parts σ
    (build_tuple_nested_binder_wild_path_bridge_certificate ps vs parts σ H).

Lemma tuple_nested_binder_wild_generated_part_list_witness_to_path_correspondence_witness :
  forall ps vs parts σ,
    tuple_nested_binder_wild_generated_part_list_witness ps vs parts σ ->
    tuple_nested_binder_wild_path_correspondence_witness ps vs parts σ.
Proof.
  intros ps vs parts σ H.
  exact (build_tuple_nested_binder_wild_path_correspondence_witness ps vs parts σ H).
Qed.

Lemma struct_nested_binder_wild_generated_part_list_witness_to_path_correspondence_witness_of_bridge :
  forall name fs vs parts σ,
    struct_nested_binder_wild_generated_part_list_witness name fs vs parts σ ->
    struct_nested_binder_wild_path_bridge_assumption fs ->
    struct_nested_binder_wild_path_correspondence_witness name fs vs parts σ.
Proof.
  intros name fs vs parts σ H Hbridge.
  split.
  - exact H.
  - rewrite (struct_nested_binder_wild_generated_part_list_witness_subst_domain name fs vs parts σ H).
    symmetry. exact Hbridge.
Qed.

Lemma struct_nested_binder_wild_path_bridge_certificate_to_path_correspondence_witness :
  forall name fs vs parts σ,
    struct_nested_binder_wild_path_bridge_certificate name fs vs parts σ ->
    struct_nested_binder_wild_path_correspondence_witness name fs vs parts σ.
Proof.
  intros name fs vs parts σ H.
  destruct H as [Hparts Hbridge].
  exact (struct_nested_binder_wild_generated_part_list_witness_to_path_correspondence_witness_of_bridge
    name fs vs parts σ Hparts Hbridge).
Qed.

Definition build_struct_nested_binder_wild_path_correspondence_witness
    (name : string) (fs : list (string * pattern)) (vs : list (string * value))
    (parts : list subst) (σ : subst)
    (H : struct_nested_binder_wild_generated_part_list_witness name fs vs parts σ)
  : struct_nested_binder_wild_path_correspondence_witness name fs vs parts σ :=
  struct_nested_binder_wild_path_bridge_certificate_to_path_correspondence_witness
    name fs vs parts σ
    (build_struct_nested_binder_wild_path_bridge_certificate name fs vs parts σ H).

Lemma struct_nested_binder_wild_generated_part_list_witness_to_path_correspondence_witness :
  forall name fs vs parts σ,
    struct_nested_binder_wild_generated_part_list_witness name fs vs parts σ ->
    struct_nested_binder_wild_path_correspondence_witness name fs vs parts σ.
Proof.
  intros name fs vs parts σ H.
  exact (build_struct_nested_binder_wild_path_correspondence_witness name fs vs parts σ H).
Qed.

Lemma binder_path_name_membership_of_domain_eq :
  forall bs σ,
    subst_domain σ = binder_path_binding_names bs ->
    binder_path_name_membership_witness bs σ.
Proof.
  intros bs σ Heq x. rewrite Heq. tauto.
Qed.

Lemma binder_path_name_length_of_domain_eq :
  forall bs σ,
    subst_domain σ = binder_path_binding_names bs ->
    binder_path_name_length_witness bs σ.
Proof.
  intros bs σ Heq. unfold binder_path_name_length_witness. now rewrite Heq.
Qed.

Lemma binder_path_binding_name_of_mem :
  forall bs b,
    In b bs ->
    In (snd b) (binder_path_binding_names bs).
Proof.
  intros bs b Hb.
  induction bs as [| b' bs IH].
  - contradiction.
  - simpl in Hb |- *.
    destruct Hb as [Heq | Hrest].
    + subst. simpl. auto.
    + right. exact (IH Hrest).
Qed.

Lemma binder_path_binding_exists_of_name_mem :
  forall bs x,
    In x (binder_path_binding_names bs) ->
    exists path, In (path, x) bs.
Proof.
  induction bs as [| [path y] bs IH]; intros x Hx.
  - contradiction.
  - simpl in Hx.
    destruct Hx as [Hxy | Hrest].
    + subst. exists path. simpl. auto.
    + destruct (IH _ Hrest) as [path' Hmem].
      exists path'. simpl. auto.
Qed.

Lemma binder_path_coverage_of_domain_eq :
  forall bs σ,
    subst_domain σ = binder_path_binding_names bs ->
    binder_path_coverage_witness bs σ.
Proof.
  intros bs σ Heq. split.
  - intros b Hb.
    rewrite Heq.
    exact (binder_path_binding_name_of_mem bs b Hb).
  - intros x Hx.
    rewrite Heq in Hx.
    exact (binder_path_binding_exists_of_name_mem bs x Hx).
Qed.

Lemma binder_path_domain_coverage_of_names_eq :
  forall bs dom,
    binder_path_binding_names bs = dom ->
    binder_path_domain_coverage_witness bs dom.
Proof.
  intros bs dom Heq. split.
  - intros b Hb.
    rewrite <- Heq.
    exact (binder_path_binding_name_of_mem bs b Hb).
  - intros x Hx.
    rewrite <- Heq in Hx.
    exact (binder_path_binding_exists_of_name_mem bs x Hx).
Qed.

Lemma binder_path_leaf_of_domain_eq_domain_coverage :
  forall bs σ dom,
    subst_domain σ = binder_path_binding_names bs ->
    binder_path_domain_coverage_witness bs dom ->
    binder_path_leaf_witness bs σ dom.
Proof.
  intros bs σ dom Heq Hdom x Hx.
  destruct Hdom as [_ Hback].
  destruct (Hback x Hx) as [path Hmem].
  split.
  - rewrite Heq.
    exact (binder_path_binding_name_of_mem bs (path, x) Hmem).
  - exists path. exact Hmem.
Qed.

Lemma mem_merge_subst_domains_exists_part :
  forall parts x,
    In x (merge_subst_domains parts) ->
    exists part, In part parts /\ In x (subst_domain part).
Proof.
  induction parts as [| part parts IH]; intros x Hx.
  - contradiction.
  - simpl in Hx.
    rewrite in_app_iff in Hx.
    destruct Hx as [Hhead | Htail].
    + exists part. split.
      * simpl. auto.
      * exact Hhead.
    + destruct (IH _ Htail) as [part' [Hmem Hxpart]].
      exists part'. split.
      * simpl. auto.
      * exact Hxpart.
Qed.

Lemma binder_path_part_leaf_of_domain_coverage_merge_domains :
  forall bs parts dom,
    binder_path_domain_coverage_witness bs dom ->
    merge_subst_domains parts = dom ->
    binder_path_part_leaf_witness bs parts dom.
Proof.
  intros bs parts dom Hdom Hparts x Hx.
  split.
  - exact (proj2 Hdom x Hx).
  - assert (Hmerge : In x (merge_subst_domains parts)).
    { rewrite Hparts. exact Hx. }
    exact (mem_merge_subst_domains_exists_part parts x Hmerge).
Qed.

Lemma binder_path_part_origin_of_part_leaf :
  forall bs parts dom,
    binder_path_part_leaf_witness bs parts dom ->
    binder_path_part_origin_witness bs parts dom.
Proof.
  intros bs parts dom H x Hx.
  destruct (H x Hx) as [[path Hpath] [part [Hpart Hxpart]]].
  exists path, part.
  repeat split; assumption.
Qed.


Lemma subst_binding_exists_of_domain_mem :
  forall part x,
    In x (subst_domain part) ->
    exists value, In (x, value) part.
Proof.
  induction part as [| [y value] part IH]; intros x Hx.
  - contradiction.
  - simpl in Hx.
    destruct Hx as [Hxy | Htail].
    + subst. exists value. simpl. auto.
    + destruct (IH _ Htail) as [value' Hmem].
      exists value'. simpl. auto.
Qed.

Lemma binder_path_value_origin_of_part_origin :
  forall bs parts dom,
    binder_path_part_origin_witness bs parts dom ->
    binder_path_value_origin_witness bs parts dom.
Proof.
  intros bs parts dom H x Hx.
  destruct (H x Hx) as [path [part [Hpath [Hpart Hxpart]]]].
  destruct (subst_binding_exists_of_domain_mem part x Hxpart) as [value Hbind].
  exists path, part, value.
  repeat split; assumption.
Qed.

Lemma nested_binder_wild_pattern_binder_path_bindings_domain_coverage :
  forall p path,
    nested_binder_wild_pattern p ->
    binder_path_domain_coverage_witness
      (nested_binder_wild_pattern_binder_path_bindings p path)
      (nested_binder_wild_pattern_domain p).
Proof.
  intros p path Hfrag.
  apply binder_path_domain_coverage_of_names_eq.
  apply nested_binder_wild_pattern_binder_path_bindings_names.
  exact Hfrag.
Qed.

Lemma nested_binder_wild_pattern_list_binder_path_bindings_domain_coverage :
  forall ps path idx,
    nested_binder_wild_pattern_list ps ->
    binder_path_domain_coverage_witness
      (nested_binder_wild_pattern_list_binder_path_bindings ps path idx)
      (nested_binder_wild_pattern_list_domain ps).
Proof.
  intros ps path idx Hfrag.
  apply binder_path_domain_coverage_of_names_eq.
  apply nested_binder_wild_pattern_list_binder_path_bindings_names.
  exact Hfrag.
Qed.

Lemma nested_binder_wild_struct_field_binder_path_bindings_domain_coverage :
  forall fs path,
    nested_binder_wild_struct_field_pattern_list fs ->
    binder_path_domain_coverage_witness
      (nested_binder_wild_struct_field_binder_path_bindings fs path)
      (nested_binder_wild_struct_field_pattern_list_domain fs).
Proof.
  intros fs path Hfrag.
  apply binder_path_domain_coverage_of_names_eq.
  apply nested_binder_wild_struct_field_binder_path_bindings_names.
  exact Hfrag.
Qed.

Lemma tuple_nested_binder_wild_path_correspondence_witness_to_summary_witness :
  forall ps vs parts σ,
    tuple_nested_binder_wild_path_correspondence_witness ps vs parts σ ->
    tuple_nested_binder_wild_path_summary_witness ps vs parts σ.
Proof.
  intros ps vs parts σ H.
  destruct H as [Hbase Heq].
  split.
  - split; assumption.
  - split.
    + exact (binder_path_name_membership_of_domain_eq
        (nested_binder_wild_pattern_list_binder_path_bindings ps [] 0) σ Heq).
    + exact (binder_path_name_length_of_domain_eq
        (nested_binder_wild_pattern_list_binder_path_bindings ps [] 0) σ Heq).
Qed.

Lemma struct_nested_binder_wild_path_correspondence_witness_to_summary_witness :
  forall name fs vs parts σ,
    struct_nested_binder_wild_path_correspondence_witness name fs vs parts σ ->
    struct_nested_binder_wild_path_summary_witness name fs vs parts σ.
Proof.
  intros name fs vs parts σ H.
  destruct H as [Hbase Heq].
  split.
  - split; assumption.
  - split.
    + exact (binder_path_name_membership_of_domain_eq
        (nested_binder_wild_struct_field_binder_path_bindings fs []) σ Heq).
    + exact (binder_path_name_length_of_domain_eq
        (nested_binder_wild_struct_field_binder_path_bindings fs []) σ Heq).
Qed.

Lemma tuple_nested_binder_wild_path_correspondence_witness_to_coverage_witness :
  forall ps vs parts σ,
    tuple_nested_binder_wild_path_correspondence_witness ps vs parts σ ->
    tuple_nested_binder_wild_path_coverage_witness ps vs parts σ.
Proof.
  intros ps vs parts σ H.
  destruct H as [Hbase Heq].
  split.
  - split; assumption.
  - exact (binder_path_coverage_of_domain_eq
      (nested_binder_wild_pattern_list_binder_path_bindings ps [] 0) σ Heq).
Qed.

Lemma struct_nested_binder_wild_path_correspondence_witness_to_coverage_witness :
  forall name fs vs parts σ,
    struct_nested_binder_wild_path_correspondence_witness name fs vs parts σ ->
    struct_nested_binder_wild_path_coverage_witness name fs vs parts σ.
Proof.
  intros name fs vs parts σ H.
  destruct H as [Hbase Heq].
  split.
  - split; assumption.
  - exact (binder_path_coverage_of_domain_eq
      (nested_binder_wild_struct_field_binder_path_bindings fs []) σ Heq).
Qed.

Definition build_tuple_nested_binder_wild_path_summary_witness
    (ps : list pattern) (vs : list value) (parts : list subst) (σ : subst)
    (H : tuple_nested_binder_wild_generated_part_list_witness ps vs parts σ)
  : tuple_nested_binder_wild_path_summary_witness ps vs parts σ :=
  tuple_nested_binder_wild_path_correspondence_witness_to_summary_witness
    ps vs parts σ (build_tuple_nested_binder_wild_path_correspondence_witness ps vs parts σ H).

Definition build_struct_nested_binder_wild_path_summary_witness
    (name : string) (fs : list (string * pattern)) (vs : list (string * value))
    (parts : list subst) (σ : subst)
    (H : struct_nested_binder_wild_generated_part_list_witness name fs vs parts σ)
  : struct_nested_binder_wild_path_summary_witness name fs vs parts σ :=
  struct_nested_binder_wild_path_correspondence_witness_to_summary_witness
    name fs vs parts σ
    (build_struct_nested_binder_wild_path_correspondence_witness name fs vs parts σ H).

Definition build_tuple_nested_binder_wild_path_coverage_witness
    (ps : list pattern) (vs : list value) (parts : list subst) (σ : subst)
    (H : tuple_nested_binder_wild_generated_part_list_witness ps vs parts σ)
  : tuple_nested_binder_wild_path_coverage_witness ps vs parts σ :=
  tuple_nested_binder_wild_path_correspondence_witness_to_coverage_witness
    ps vs parts σ (build_tuple_nested_binder_wild_path_correspondence_witness ps vs parts σ H).

Definition build_struct_nested_binder_wild_path_coverage_witness
    (name : string) (fs : list (string * pattern)) (vs : list (string * value))
    (parts : list subst) (σ : subst)
    (H : struct_nested_binder_wild_generated_part_list_witness name fs vs parts σ)
  : struct_nested_binder_wild_path_coverage_witness name fs vs parts σ :=
  struct_nested_binder_wild_path_correspondence_witness_to_coverage_witness
    name fs vs parts σ
    (build_struct_nested_binder_wild_path_correspondence_witness name fs vs parts σ H).

Definition build_tuple_nested_binder_wild_path_witness_bundle_with_provider
    (ps : list pattern) (vs : list value) (parts : list subst) (σ : subst)
    (P : tuple_nested_binder_wild_path_bridge_provider ps)
    (H : tuple_nested_binder_wild_generated_part_list_witness ps vs parts σ)
  : tuple_nested_binder_wild_path_witness_bundle ps vs parts σ :=
  match H with
  | conj Hfrag _ =>
      {| tnpwb_bridge := build_tuple_nested_binder_wild_path_bridge_certificate_with_provider ps vs parts σ P H;
         tnpwb_correspondence := tuple_nested_binder_wild_path_bridge_certificate_to_path_correspondence_witness
           ps vs parts σ (build_tuple_nested_binder_wild_path_bridge_certificate_with_provider ps vs parts σ P H);
         tnpwb_summary := tuple_nested_binder_wild_path_correspondence_witness_to_summary_witness
           ps vs parts σ
           (tuple_nested_binder_wild_path_bridge_certificate_to_path_correspondence_witness
             ps vs parts σ (build_tuple_nested_binder_wild_path_bridge_certificate_with_provider ps vs parts σ P H));
         tnpwb_coverage := tuple_nested_binder_wild_path_correspondence_witness_to_coverage_witness
           ps vs parts σ
           (tuple_nested_binder_wild_path_bridge_certificate_to_path_correspondence_witness
             ps vs parts σ (build_tuple_nested_binder_wild_path_bridge_certificate_with_provider ps vs parts σ P H));
         tnpwb_domain_coverage := nested_binder_wild_pattern_list_binder_path_bindings_domain_coverage ps [] 0 Hfrag;
         tnpwb_leaf := binder_path_leaf_of_domain_eq_domain_coverage
           (nested_binder_wild_pattern_list_binder_path_bindings ps [] 0)
           σ
           (nested_binder_wild_pattern_list_domain ps)
           (proj2 (tuple_nested_binder_wild_path_bridge_certificate_to_path_correspondence_witness
             ps vs parts σ (build_tuple_nested_binder_wild_path_bridge_certificate_with_provider ps vs parts σ P H)))
           (nested_binder_wild_pattern_list_binder_path_bindings_domain_coverage ps [] 0 Hfrag);
         tnpwb_part_leaf := binder_path_part_leaf_of_domain_coverage_merge_domains
           (nested_binder_wild_pattern_list_binder_path_bindings ps [] 0)
           parts
           (nested_binder_wild_pattern_list_domain ps)
           (nested_binder_wild_pattern_list_binder_path_bindings_domain_coverage ps [] 0 Hfrag)
           (tuple_nested_binder_wild_generated_part_list_witness_domain ps vs parts σ H);
         tnpwb_origin := binder_path_part_origin_of_part_leaf
           (nested_binder_wild_pattern_list_binder_path_bindings ps [] 0)
           parts
           (nested_binder_wild_pattern_list_domain ps)
           (binder_path_part_leaf_of_domain_coverage_merge_domains
             (nested_binder_wild_pattern_list_binder_path_bindings ps [] 0)
             parts
             (nested_binder_wild_pattern_list_domain ps)
             (nested_binder_wild_pattern_list_binder_path_bindings_domain_coverage ps [] 0 Hfrag)
             (tuple_nested_binder_wild_generated_part_list_witness_domain ps vs parts σ H));
         tnpwb_value_origin := binder_path_value_origin_of_part_origin
           (nested_binder_wild_pattern_list_binder_path_bindings ps [] 0)
           parts
           (nested_binder_wild_pattern_list_domain ps)
           (binder_path_part_origin_of_part_leaf
             (nested_binder_wild_pattern_list_binder_path_bindings ps [] 0)
             parts
             (nested_binder_wild_pattern_list_domain ps)
             (binder_path_part_leaf_of_domain_coverage_merge_domains
               (nested_binder_wild_pattern_list_binder_path_bindings ps [] 0)
               parts
               (nested_binder_wild_pattern_list_domain ps)
               (nested_binder_wild_pattern_list_binder_path_bindings_domain_coverage ps [] 0 Hfrag)
               (tuple_nested_binder_wild_generated_part_list_witness_domain ps vs parts σ H))) |}
  end.

Definition build_struct_nested_binder_wild_path_witness_bundle_with_provider
    (name : string) (fs : list (string * pattern)) (vs : list (string * value))
    (parts : list subst) (σ : subst)
    (P : struct_nested_binder_wild_path_bridge_provider fs)
    (H : struct_nested_binder_wild_generated_part_list_witness name fs vs parts σ)
  : struct_nested_binder_wild_path_witness_bundle name fs vs parts σ :=
  match H with
  | conj Hfrag _ =>
      {| snpwb_bridge := build_struct_nested_binder_wild_path_bridge_certificate_with_provider name fs vs parts σ P H;
         snpwb_correspondence := struct_nested_binder_wild_path_bridge_certificate_to_path_correspondence_witness
           name fs vs parts σ (build_struct_nested_binder_wild_path_bridge_certificate_with_provider name fs vs parts σ P H);
         snpwb_summary := struct_nested_binder_wild_path_correspondence_witness_to_summary_witness
           name fs vs parts σ
           (struct_nested_binder_wild_path_bridge_certificate_to_path_correspondence_witness
             name fs vs parts σ (build_struct_nested_binder_wild_path_bridge_certificate_with_provider name fs vs parts σ P H));
         snpwb_coverage := struct_nested_binder_wild_path_correspondence_witness_to_coverage_witness
           name fs vs parts σ
           (struct_nested_binder_wild_path_bridge_certificate_to_path_correspondence_witness
             name fs vs parts σ (build_struct_nested_binder_wild_path_bridge_certificate_with_provider name fs vs parts σ P H));
         snpwb_domain_coverage := nested_binder_wild_struct_field_binder_path_bindings_domain_coverage fs [] Hfrag;
         snpwb_leaf := binder_path_leaf_of_domain_eq_domain_coverage
           (nested_binder_wild_struct_field_binder_path_bindings fs [])
           σ
           (nested_binder_wild_struct_field_pattern_list_domain fs)
           (proj2 (struct_nested_binder_wild_path_bridge_certificate_to_path_correspondence_witness
             name fs vs parts σ (build_struct_nested_binder_wild_path_bridge_certificate_with_provider name fs vs parts σ P H)))
           (nested_binder_wild_struct_field_binder_path_bindings_domain_coverage fs [] Hfrag);
         snpwb_part_leaf := binder_path_part_leaf_of_domain_coverage_merge_domains
           (nested_binder_wild_struct_field_binder_path_bindings fs [])
           parts
           (nested_binder_wild_struct_field_pattern_list_domain fs)
           (nested_binder_wild_struct_field_binder_path_bindings_domain_coverage fs [] Hfrag)
           (struct_nested_binder_wild_generated_part_list_witness_domain name fs vs parts σ H);
         snpwb_origin := binder_path_part_origin_of_part_leaf
           (nested_binder_wild_struct_field_binder_path_bindings fs [])
           parts
           (nested_binder_wild_struct_field_pattern_list_domain fs)
           (binder_path_part_leaf_of_domain_coverage_merge_domains
             (nested_binder_wild_struct_field_binder_path_bindings fs [])
             parts
             (nested_binder_wild_struct_field_pattern_list_domain fs)
             (nested_binder_wild_struct_field_binder_path_bindings_domain_coverage fs [] Hfrag)
             (struct_nested_binder_wild_generated_part_list_witness_domain name fs vs parts σ H));
         snpwb_value_origin := binder_path_value_origin_of_part_origin
           (nested_binder_wild_struct_field_binder_path_bindings fs [])
           parts
           (nested_binder_wild_struct_field_pattern_list_domain fs)
           (binder_path_part_origin_of_part_leaf
             (nested_binder_wild_struct_field_binder_path_bindings fs [])
             parts
             (nested_binder_wild_struct_field_pattern_list_domain fs)
             (binder_path_part_leaf_of_domain_coverage_merge_domains
               (nested_binder_wild_struct_field_binder_path_bindings fs [])
               parts
               (nested_binder_wild_struct_field_pattern_list_domain fs)
               (nested_binder_wild_struct_field_binder_path_bindings_domain_coverage fs [] Hfrag)
               (struct_nested_binder_wild_generated_part_list_witness_domain name fs vs parts σ H))) |}
  end.

Definition build_tuple_nested_binder_wild_path_witness_bundle
    (ps : list pattern) (vs : list value) (parts : list subst) (σ : subst)
    (H : tuple_nested_binder_wild_generated_part_list_witness ps vs parts σ)
  : tuple_nested_binder_wild_path_witness_bundle ps vs parts σ :=
  build_tuple_nested_binder_wild_path_witness_bundle_with_provider
    ps vs parts σ
    (build_tuple_nested_binder_wild_path_bridge_provider_of_witness ps vs parts σ H) H.

Definition build_tuple_nested_binder_wild_path_witness_bundle_of_generated
    (ps : list pattern) (vs : list value) (parts : list subst)
    (Hfrag : nested_binder_wild_pattern_list ps)
    (Hparts : tuple_nested_binder_wild_generated_parts ps vs parts)
  : tuple_nested_binder_wild_path_witness_bundle ps vs parts (merge_substs parts) :=
  build_tuple_nested_binder_wild_path_witness_bundle_with_provider
    ps vs parts (merge_substs parts)
    (build_tuple_nested_binder_wild_path_bridge_provider_of_generated ps vs parts Hfrag Hparts)
    (tuple_nested_binder_wild_generated_part_list_witness_of_generated ps vs parts Hfrag Hparts).

Definition build_struct_nested_binder_wild_path_witness_bundle
    (name : string) (fs : list (string * pattern)) (vs : list (string * value))
    (parts : list subst) (σ : subst)
    (H : struct_nested_binder_wild_generated_part_list_witness name fs vs parts σ)
  : struct_nested_binder_wild_path_witness_bundle name fs vs parts σ :=
  build_struct_nested_binder_wild_path_witness_bundle_with_provider
    name fs vs parts σ
    (build_struct_nested_binder_wild_path_bridge_provider_of_witness
      name fs vs parts σ H) H.

Definition build_struct_nested_binder_wild_path_witness_bundle_of_generated
    (name : string) (fs : list (string * pattern)) (vs : list (string * value))
    (parts : list subst)
    (Hfrag : nested_binder_wild_struct_field_pattern_list fs)
    (Hparts : struct_nested_binder_wild_generated_parts fs vs parts)
  : struct_nested_binder_wild_path_witness_bundle name fs vs parts (merge_substs parts) :=
  build_struct_nested_binder_wild_path_witness_bundle_with_provider
    name fs vs parts (merge_substs parts)
    (build_struct_nested_binder_wild_path_bridge_provider_of_generated
      name fs vs parts Hfrag Hparts)
    (struct_nested_binder_wild_generated_part_list_witness_of_generated
      name fs vs parts Hfrag Hparts).

Lemma struct_pattern_composition_spine_to_composition :
  forall name fs vs σ,
    struct_pattern_composition_spine name fs vs σ ->
    subst_composition σ.
Proof.
  intros name fs vs σ H.
  destruct H as [parts [_ [_ [Hmerge Hdom]]]].
  exists parts. split; assumption.
Qed.

Lemma struct_pattern_composition_spine_exact :
  forall (name : string) (fs : list (string * pattern)) (vs : list (string * value)) (σ : subst),
    List.length fs = List.length vs ->
    struct_pattern_composition_spine name fs vs σ.
Proof.
  intros name fs vs σ Hshape.
  exists ((repeat ([] : subst) (List.length fs) ++ [σ])%list).
  repeat split.
  - rewrite app_length, repeat_length. simpl. lia.
  - rewrite app_length, repeat_length. simpl. lia.
  - apply merge_substs_repeat_nil_singleton.
  - apply merge_subst_domains_repeat_nil_singleton.
Qed.

Lemma struct_pattern_recursive_composition_witness_to_spine :
  forall name fs vs σ,
    struct_pattern_recursive_composition_witness name fs vs σ ->
    struct_pattern_composition_spine name fs vs σ.
Proof.
  intros name fs vs σ H.
  destruct H as [parts [Hfs [Hvs [_ [Hmerge Hdom]]]]].
  exists ((parts ++ [σ])%list). repeat split.
  - rewrite app_length. simpl. lia.
  - rewrite app_length. simpl. lia.
  - exact Hmerge.
  - exact Hdom.
Qed.

Lemma struct_pattern_recursive_composition_witness_exact :
  forall (name : string) (fs : list (string * pattern)) (vs : list (string * value)) (σ : subst),
    List.length fs = List.length vs ->
    struct_pattern_recursive_composition_witness name fs vs σ.
Proof.
  intros name fs vs σ Hshape.
  exists (repeat ([] : subst) (List.length fs)).
  repeat split.
  - rewrite repeat_length. reflexivity.
  - rewrite repeat_length. exact Hshape.
  - apply forall_repeat_nil_subst.
  - apply merge_substs_repeat_nil_singleton.
  - apply merge_subst_domains_repeat_nil_singleton.
Qed.

Theorem pattern_binds_unique :
  forall p v σ,
    pattern_match p v σ ->
    subst_unique σ.
Proof.
  intros p v σ H.
  inversion H; subst.
  - apply subst_unique_nil.
  - apply subst_unique_singleton.
  - assumption.
  - assumption.
  - assumption.
Qed.

Theorem pattern_match_sound :
  forall p v σ,
    pattern_match p v σ ->
    True.
Proof.
  intros. exact I.
Qed.

End FoPattern.
