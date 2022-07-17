(* Auto-generated from "logic.atd" *)
[@@@ocaml.warning "-27-32-33-35-39"]

type bkind = Logic_t.bkind

type logcon = Logic_t.logcon

type name = Logic_t.name

type pkind = Logic_t.pkind

type uid = Logic_t.uid

type ctxt = Logic_t.ctxt = { kind: pkind; handle: uid }

type ipath = Logic_t.ipath = { root: uid; ctxt: ctxt; sub: int list }

type vname = Logic_t.vname

type type_ = Logic_t.type_

type expr = Logic_t.expr

type form = Logic_t.form

type choice = Logic_t.choice

type itrace = Logic_t.itrace

type action = Logic_t.action

type atree = Logic_t.atree

type term = Logic_t.term

type arity = Logic_t.arity

type sig_ = Logic_t.sig_

type bvar = Logic_t.bvar

type env = Logic_t.env = {
  env_prp: (name * arity) list;
  env_fun: (name * sig_) list;
  env_var: (name * bvar list) list;
  env_tvar: (name * type_ option list) list;
  env_handles: (vname * uid) list
}

type goal = Logic_t.goal

let _4_tag = Bi_io.array_tag
let write_untagged__4 = (
  Atdgen_runtime.Ob_run.write_untagged_list
    Bi_io.svint_tag
    (
      Bi_io.write_untagged_svint
    )
)
let write__4 ob x =
  Bi_io.write_tag ob Bi_io.array_tag;
  write_untagged__4 ob x
let string_of__4 ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write__4 ob x;
  Bi_outbuf.contents ob
let get__4_reader = (
  Atdgen_runtime.Ob_run.get_list_reader (
    Atdgen_runtime.Ob_run.get_int_reader
  )
)
let read__4 = (
  Atdgen_runtime.Ob_run.read_list (
    Atdgen_runtime.Ob_run.get_int_reader
  )
)
let _4_of_string ?pos s =
  read__4 (Bi_inbuf.from_string ?pos s)
let bkind_tag = Bi_io.variant_tag
let write_untagged_bkind = (
  fun ob x ->
    match x with
      | `Forall -> Bi_outbuf.add_char4 ob '2' '\025' '\241' '\216'
      | `Exist -> Bi_outbuf.add_char4 ob '\n' 'G' '\178' '\151'
)
let write_bkind ob x =
  Bi_io.write_tag ob Bi_io.variant_tag;
  write_untagged_bkind ob x
let string_of_bkind ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_bkind ob x;
  Bi_outbuf.contents ob
let get_bkind_reader = (
  fun tag ->
    if tag <> 23 then Atdgen_runtime.Ob_run.read_error () else
      fun ib ->
        Bi_io.read_hashtag ib (fun ib h has_arg ->
          match h, has_arg with
            | 840561112, false -> `Forall
            | 172470935, false -> `Exist
            | _ -> Atdgen_runtime.Ob_run.unsupported_variant h has_arg
        )
)
let read_bkind = (
  fun ib ->
    if Bi_io.read_tag ib <> 23 then Atdgen_runtime.Ob_run.read_error_at ib;
    Bi_io.read_hashtag ib (fun ib h has_arg ->
      match h, has_arg with
        | 840561112, false -> `Forall
        | 172470935, false -> `Exist
        | _ -> Atdgen_runtime.Ob_run.unsupported_variant h has_arg
    )
)
let bkind_of_string ?pos s =
  read_bkind (Bi_inbuf.from_string ?pos s)
let logcon_tag = Bi_io.variant_tag
let write_untagged_logcon = (
  fun ob x ->
    match x with
      | `And -> Bi_outbuf.add_char4 ob '\000' '1' '\178' '\183'
      | `Or -> Bi_outbuf.add_char4 ob '\000' '\000' 'E' 'C'
      | `Imp -> Bi_outbuf.add_char4 ob '\000' '7' '\195' '\236'
      | `Equiv -> Bi_outbuf.add_char4 ob '\005' '\176' 'F' '\150'
      | `Not -> Bi_outbuf.add_char4 ob '\000' ';' '\144' '\243'
)
let write_logcon ob x =
  Bi_io.write_tag ob Bi_io.variant_tag;
  write_untagged_logcon ob x
let string_of_logcon ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_logcon ob x;
  Bi_outbuf.contents ob
let get_logcon_reader = (
  fun tag ->
    if tag <> 23 then Atdgen_runtime.Ob_run.read_error () else
      fun ib ->
        Bi_io.read_hashtag ib (fun ib h has_arg ->
          match h, has_arg with
            | 3257015, false -> `And
            | 17731, false -> `Or
            | 3654636, false -> `Imp
            | 95438486, false -> `Equiv
            | 3903731, false -> `Not
            | _ -> Atdgen_runtime.Ob_run.unsupported_variant h has_arg
        )
)
let read_logcon = (
  fun ib ->
    if Bi_io.read_tag ib <> 23 then Atdgen_runtime.Ob_run.read_error_at ib;
    Bi_io.read_hashtag ib (fun ib h has_arg ->
      match h, has_arg with
        | 3257015, false -> `And
        | 17731, false -> `Or
        | 3654636, false -> `Imp
        | 95438486, false -> `Equiv
        | 3903731, false -> `Not
        | _ -> Atdgen_runtime.Ob_run.unsupported_variant h has_arg
    )
)
let logcon_of_string ?pos s =
  read_logcon (Bi_inbuf.from_string ?pos s)
let name_tag = Bi_io.string_tag
let write_untagged_name = (
  Bi_io.write_untagged_string
)
let write_name ob x =
  Bi_io.write_tag ob Bi_io.string_tag;
  write_untagged_name ob x
let string_of_name ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_name ob x;
  Bi_outbuf.contents ob
let get_name_reader = (
  Atdgen_runtime.Ob_run.get_string_reader
)
let read_name = (
  Atdgen_runtime.Ob_run.read_string
)
let name_of_string ?pos s =
  read_name (Bi_inbuf.from_string ?pos s)
let pkind_tag = Bi_io.variant_tag
let write_untagged_pkind = (
  fun ob x ->
    match x with
      | `Hyp -> Bi_outbuf.add_char4 ob '\000' '7' '\012' '\031'
      | `Concl -> Bi_outbuf.add_char4 ob ']' '\139' '[' 'K'
      | `Var x ->
        Bi_outbuf.add_char4 ob '\128' 'A' '\150' '\199';
        (
          fun ob x ->
            Bi_io.write_tag ob Bi_io.variant_tag;
            match x with
              | `Head -> Bi_outbuf.add_char4 ob '/' '\228' 'U' '@'
              | `Body -> Bi_outbuf.add_char4 ob '+' '\244' '\166' '\194'
        ) ob x
)
let write_pkind ob x =
  Bi_io.write_tag ob Bi_io.variant_tag;
  write_untagged_pkind ob x
let string_of_pkind ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_pkind ob x;
  Bi_outbuf.contents ob
let get_pkind_reader = (
  fun tag ->
    if tag <> 23 then Atdgen_runtime.Ob_run.read_error () else
      fun ib ->
        Bi_io.read_hashtag ib (fun ib h has_arg ->
          match h, has_arg with
            | 3607583, false -> `Hyp
            | -578069685, false -> `Concl
            | 4298439, true -> (`Var (
                (
                  fun ib ->
                    if Bi_io.read_tag ib <> 23 then Atdgen_runtime.Ob_run.read_error_at ib;
                    Bi_io.read_hashtag ib (fun ib h has_arg ->
                      match h, has_arg with
                        | 803493184, false -> `Head
                        | 737453762, false -> `Body
                        | _ -> Atdgen_runtime.Ob_run.unsupported_variant h has_arg
                    )
                ) ib
              ))
            | _ -> Atdgen_runtime.Ob_run.unsupported_variant h has_arg
        )
)
let read_pkind = (
  fun ib ->
    if Bi_io.read_tag ib <> 23 then Atdgen_runtime.Ob_run.read_error_at ib;
    Bi_io.read_hashtag ib (fun ib h has_arg ->
      match h, has_arg with
        | 3607583, false -> `Hyp
        | -578069685, false -> `Concl
        | 4298439, true -> (`Var (
            (
              fun ib ->
                if Bi_io.read_tag ib <> 23 then Atdgen_runtime.Ob_run.read_error_at ib;
                Bi_io.read_hashtag ib (fun ib h has_arg ->
                  match h, has_arg with
                    | 803493184, false -> `Head
                    | 737453762, false -> `Body
                    | _ -> Atdgen_runtime.Ob_run.unsupported_variant h has_arg
                )
            ) ib
          ))
        | _ -> Atdgen_runtime.Ob_run.unsupported_variant h has_arg
    )
)
let pkind_of_string ?pos s =
  read_pkind (Bi_inbuf.from_string ?pos s)
let uid_tag = Bi_io.svint_tag
let write_untagged_uid = (
  Bi_io.write_untagged_svint
)
let write_uid ob x =
  Bi_io.write_tag ob Bi_io.svint_tag;
  write_untagged_uid ob x
let string_of_uid ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_uid ob x;
  Bi_outbuf.contents ob
let get_uid_reader = (
  Atdgen_runtime.Ob_run.get_int_reader
)
let read_uid = (
  Atdgen_runtime.Ob_run.read_int
)
let uid_of_string ?pos s =
  read_uid (Bi_inbuf.from_string ?pos s)
let _8_tag = Bi_io.num_variant_tag
let write_untagged__8 = (
  Atdgen_runtime.Ob_run.write_untagged_option (
    write_uid
  )
)
let write__8 ob x =
  Bi_io.write_tag ob Bi_io.num_variant_tag;
  write_untagged__8 ob x
let string_of__8 ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write__8 ob x;
  Bi_outbuf.contents ob
let get__8_reader = (
  fun tag ->
    if tag <> 22 then Atdgen_runtime.Ob_run.read_error () else
      fun ib ->
        match Char.code (Bi_inbuf.read_char ib) with
          | 0 -> None
          | 0x80 ->
            Some (
              (
                read_uid
              )
                ib
            )
          | _ -> Atdgen_runtime.Ob_run.read_error_at ib
)
let read__8 = (
  fun ib ->
    if Bi_io.read_tag ib <> 22 then Atdgen_runtime.Ob_run.read_error_at ib;
    match Char.code (Bi_inbuf.read_char ib) with
      | 0 -> None
      | 0x80 ->
        Some (
          (
            read_uid
          )
            ib
        )
      | _ -> Atdgen_runtime.Ob_run.read_error_at ib
)
let _8_of_string ?pos s =
  read__8 (Bi_inbuf.from_string ?pos s)
let ctxt_tag = Bi_io.record_tag
let write_untagged_ctxt : Bi_outbuf.t -> ctxt -> unit = (
  fun ob x ->
    Bi_vint.write_uvint ob 2;
    Bi_outbuf.add_char4 ob '\199' '\t' '\225' 'T';
    (
      write_pkind
    ) ob x.kind;
    Bi_outbuf.add_char4 ob '\183' '\253' '\131' '\168';
    (
      write_uid
    ) ob x.handle;
)
let write_ctxt ob x =
  Bi_io.write_tag ob Bi_io.record_tag;
  write_untagged_ctxt ob x
let string_of_ctxt ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_ctxt ob x;
  Bi_outbuf.contents ob
let get_ctxt_reader = (
  fun tag ->
    if tag <> 21 then Atdgen_runtime.Ob_run.read_error () else
      fun ib ->
        let field_kind = ref (Obj.magic (Sys.opaque_identity 0.0)) in
        let field_handle = ref (Obj.magic (Sys.opaque_identity 0.0)) in
        let bits0 = ref 0 in
        let len = Bi_vint.read_uvint ib in
        for i = 1 to len do
          match Bi_io.read_field_hashtag ib with
            | -955653804 ->
              field_kind := (
                (
                  read_pkind
                ) ib
              );
              bits0 := !bits0 lor 0x1;
            | 939361192 ->
              field_handle := (
                (
                  read_uid
                ) ib
              );
              bits0 := !bits0 lor 0x2;
            | _ -> Bi_io.skip ib
        done;
        if !bits0 <> 0x3 then Atdgen_runtime.Ob_run.missing_fields [| !bits0 |] [| "kind"; "handle" |];
        (
          {
            kind = !field_kind;
            handle = !field_handle;
          }
         : ctxt)
)
let read_ctxt = (
  fun ib ->
    if Bi_io.read_tag ib <> 21 then Atdgen_runtime.Ob_run.read_error_at ib;
    let field_kind = ref (Obj.magic (Sys.opaque_identity 0.0)) in
    let field_handle = ref (Obj.magic (Sys.opaque_identity 0.0)) in
    let bits0 = ref 0 in
    let len = Bi_vint.read_uvint ib in
    for i = 1 to len do
      match Bi_io.read_field_hashtag ib with
        | -955653804 ->
          field_kind := (
            (
              read_pkind
            ) ib
          );
          bits0 := !bits0 lor 0x1;
        | 939361192 ->
          field_handle := (
            (
              read_uid
            ) ib
          );
          bits0 := !bits0 lor 0x2;
        | _ -> Bi_io.skip ib
    done;
    if !bits0 <> 0x3 then Atdgen_runtime.Ob_run.missing_fields [| !bits0 |] [| "kind"; "handle" |];
    (
      {
        kind = !field_kind;
        handle = !field_handle;
      }
     : ctxt)
)
let ctxt_of_string ?pos s =
  read_ctxt (Bi_inbuf.from_string ?pos s)
let ipath_tag = Bi_io.record_tag
let write_untagged_ipath : Bi_outbuf.t -> ipath -> unit = (
  fun ob x ->
    Bi_vint.write_uvint ob 3;
    Bi_outbuf.add_char4 ob '\203' '\174' '\238' '"';
    (
      write_uid
    ) ob x.root;
    Bi_outbuf.add_char4 ob '\193' '\200' '\141' '\237';
    (
      write_ctxt
    ) ob x.ctxt;
    Bi_outbuf.add_char4 ob '\128' 'W' '\169' '\128';
    (
      write__4
    ) ob x.sub;
)
let write_ipath ob x =
  Bi_io.write_tag ob Bi_io.record_tag;
  write_untagged_ipath ob x
let string_of_ipath ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_ipath ob x;
  Bi_outbuf.contents ob
let get_ipath_reader = (
  fun tag ->
    if tag <> 21 then Atdgen_runtime.Ob_run.read_error () else
      fun ib ->
        let field_root = ref (Obj.magic (Sys.opaque_identity 0.0)) in
        let field_ctxt = ref (Obj.magic (Sys.opaque_identity 0.0)) in
        let field_sub = ref (Obj.magic (Sys.opaque_identity 0.0)) in
        let bits0 = ref 0 in
        let len = Bi_vint.read_uvint ib in
        for i = 1 to len do
          match Bi_io.read_field_hashtag ib with
            | -877728222 ->
              field_root := (
                (
                  read_uid
                ) ib
              );
              bits0 := !bits0 lor 0x1;
            | -1043821075 ->
              field_ctxt := (
                (
                  read_ctxt
                ) ib
              );
              bits0 := !bits0 lor 0x2;
            | 5745024 ->
              field_sub := (
                (
                  read__4
                ) ib
              );
              bits0 := !bits0 lor 0x4;
            | _ -> Bi_io.skip ib
        done;
        if !bits0 <> 0x7 then Atdgen_runtime.Ob_run.missing_fields [| !bits0 |] [| "root"; "ctxt"; "sub" |];
        (
          {
            root = !field_root;
            ctxt = !field_ctxt;
            sub = !field_sub;
          }
         : ipath)
)
let read_ipath = (
  fun ib ->
    if Bi_io.read_tag ib <> 21 then Atdgen_runtime.Ob_run.read_error_at ib;
    let field_root = ref (Obj.magic (Sys.opaque_identity 0.0)) in
    let field_ctxt = ref (Obj.magic (Sys.opaque_identity 0.0)) in
    let field_sub = ref (Obj.magic (Sys.opaque_identity 0.0)) in
    let bits0 = ref 0 in
    let len = Bi_vint.read_uvint ib in
    for i = 1 to len do
      match Bi_io.read_field_hashtag ib with
        | -877728222 ->
          field_root := (
            (
              read_uid
            ) ib
          );
          bits0 := !bits0 lor 0x1;
        | -1043821075 ->
          field_ctxt := (
            (
              read_ctxt
            ) ib
          );
          bits0 := !bits0 lor 0x2;
        | 5745024 ->
          field_sub := (
            (
              read__4
            ) ib
          );
          bits0 := !bits0 lor 0x4;
        | _ -> Bi_io.skip ib
    done;
    if !bits0 <> 0x7 then Atdgen_runtime.Ob_run.missing_fields [| !bits0 |] [| "root"; "ctxt"; "sub" |];
    (
      {
        root = !field_root;
        ctxt = !field_ctxt;
        sub = !field_sub;
      }
     : ipath)
)
let ipath_of_string ?pos s =
  read_ipath (Bi_inbuf.from_string ?pos s)
let vname_tag = Bi_io.tuple_tag
let write_untagged_vname = (
  fun ob x ->
    Bi_vint.write_uvint ob 2;
    (
      let x, _ = x in (
        write_name
      ) ob x
    );
    (
      let _, x = x in (
        Bi_io.write_svint
      ) ob x
    );
)
let write_vname ob x =
  Bi_io.write_tag ob Bi_io.tuple_tag;
  write_untagged_vname ob x
let string_of_vname ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_vname ob x;
  Bi_outbuf.contents ob
let get_vname_reader = (
  fun tag ->
    if tag <> 20 then Atdgen_runtime.Ob_run.read_error () else
      fun ib ->
        let len = Bi_vint.read_uvint ib in
        if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
        let x0 =
          (
            read_name
          ) ib
        in
        let x1 =
          (
            Atdgen_runtime.Ob_run.read_int
          ) ib
        in
        for i = 2 to len - 1 do Bi_io.skip ib done;
        (x0, x1)
)
let read_vname = (
  fun ib ->
    if Bi_io.read_tag ib <> 20 then Atdgen_runtime.Ob_run.read_error_at ib;
    let len = Bi_vint.read_uvint ib in
    if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
    let x0 =
      (
        read_name
      ) ib
    in
    let x1 =
      (
        Atdgen_runtime.Ob_run.read_int
      ) ib
    in
    for i = 2 to len - 1 do Bi_io.skip ib done;
    (x0, x1)
)
let vname_of_string ?pos s =
  read_vname (Bi_inbuf.from_string ?pos s)
let rec type__tag = Bi_io.variant_tag
and write_untagged_type_ = (
  fun ob x ->
    match x with
      | `TVar x ->
        Bi_outbuf.add_char4 ob '\183' '\199' '\130' '\243';
        (
          write_vname
        ) ob x
      | `TUnit -> Bi_outbuf.add_char4 ob '\022' '+' '\176' '\248'
      | `TProd x ->
        Bi_outbuf.add_char4 ob '\146' '\224' '\174' '\011';
        (
          fun ob x ->
            Bi_io.write_tag ob Bi_io.tuple_tag;
            Bi_vint.write_uvint ob 2;
            (
              let x, _ = x in (
                write_type_
              ) ob x
            );
            (
              let _, x = x in (
                write_type_
              ) ob x
            );
        ) ob x
      | `TOr x ->
        Bi_outbuf.add_char4 ob '\128' '@' '\002' '\151';
        (
          fun ob x ->
            Bi_io.write_tag ob Bi_io.tuple_tag;
            Bi_vint.write_uvint ob 2;
            (
              let x, _ = x in (
                write_type_
              ) ob x
            );
            (
              let _, x = x in (
                write_type_
              ) ob x
            );
        ) ob x
      | `TRec x ->
        Bi_outbuf.add_char4 ob '\183' '\196' '}' '\\';
        (
          fun ob x ->
            Bi_io.write_tag ob Bi_io.tuple_tag;
            Bi_vint.write_uvint ob 2;
            (
              let x, _ = x in (
                write_name
              ) ob x
            );
            (
              let _, x = x in (
                write_type_
              ) ob x
            );
        ) ob x
)
and write_type_ ob x =
  Bi_io.write_tag ob Bi_io.variant_tag;
  write_untagged_type_ ob x
and string_of_type_ ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_type_ ob x;
  Bi_outbuf.contents ob
let rec get_type__reader = (
  fun tag ->
    if tag <> 23 then Atdgen_runtime.Ob_run.read_error () else
      fun ib ->
        Bi_io.read_hashtag ib (fun ib h has_arg ->
          match h, has_arg with
            | 935822067, true -> (`TVar (
                (
                  read_vname
                ) ib
              ))
            | 371962104, false -> `TUnit
            | 316714507, true -> (`TProd (
                (
                  fun ib ->
                    if Bi_io.read_tag ib <> 20 then Atdgen_runtime.Ob_run.read_error_at ib;
                    let len = Bi_vint.read_uvint ib in
                    if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
                    let x0 =
                      (
                        read_type_
                      ) ib
                    in
                    let x1 =
                      (
                        read_type_
                      ) ib
                    in
                    for i = 2 to len - 1 do Bi_io.skip ib done;
                    (x0, x1)
                ) ib
              ))
            | 4194967, true -> (`TOr (
                (
                  fun ib ->
                    if Bi_io.read_tag ib <> 20 then Atdgen_runtime.Ob_run.read_error_at ib;
                    let len = Bi_vint.read_uvint ib in
                    if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
                    let x0 =
                      (
                        read_type_
                      ) ib
                    in
                    let x1 =
                      (
                        read_type_
                      ) ib
                    in
                    for i = 2 to len - 1 do Bi_io.skip ib done;
                    (x0, x1)
                ) ib
              ))
            | 935624028, true -> (`TRec (
                (
                  fun ib ->
                    if Bi_io.read_tag ib <> 20 then Atdgen_runtime.Ob_run.read_error_at ib;
                    let len = Bi_vint.read_uvint ib in
                    if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
                    let x0 =
                      (
                        read_name
                      ) ib
                    in
                    let x1 =
                      (
                        read_type_
                      ) ib
                    in
                    for i = 2 to len - 1 do Bi_io.skip ib done;
                    (x0, x1)
                ) ib
              ))
            | _ -> Atdgen_runtime.Ob_run.unsupported_variant h has_arg
        )
)
and read_type_ = (
  fun ib ->
    if Bi_io.read_tag ib <> 23 then Atdgen_runtime.Ob_run.read_error_at ib;
    Bi_io.read_hashtag ib (fun ib h has_arg ->
      match h, has_arg with
        | 935822067, true -> (`TVar (
            (
              read_vname
            ) ib
          ))
        | 371962104, false -> `TUnit
        | 316714507, true -> (`TProd (
            (
              fun ib ->
                if Bi_io.read_tag ib <> 20 then Atdgen_runtime.Ob_run.read_error_at ib;
                let len = Bi_vint.read_uvint ib in
                if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
                let x0 =
                  (
                    read_type_
                  ) ib
                in
                let x1 =
                  (
                    read_type_
                  ) ib
                in
                for i = 2 to len - 1 do Bi_io.skip ib done;
                (x0, x1)
            ) ib
          ))
        | 4194967, true -> (`TOr (
            (
              fun ib ->
                if Bi_io.read_tag ib <> 20 then Atdgen_runtime.Ob_run.read_error_at ib;
                let len = Bi_vint.read_uvint ib in
                if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
                let x0 =
                  (
                    read_type_
                  ) ib
                in
                let x1 =
                  (
                    read_type_
                  ) ib
                in
                for i = 2 to len - 1 do Bi_io.skip ib done;
                (x0, x1)
            ) ib
          ))
        | 935624028, true -> (`TRec (
            (
              fun ib ->
                if Bi_io.read_tag ib <> 20 then Atdgen_runtime.Ob_run.read_error_at ib;
                let len = Bi_vint.read_uvint ib in
                if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
                let x0 =
                  (
                    read_name
                  ) ib
                in
                let x1 =
                  (
                    read_type_
                  ) ib
                in
                for i = 2 to len - 1 do Bi_io.skip ib done;
                (x0, x1)
            ) ib
          ))
        | _ -> Atdgen_runtime.Ob_run.unsupported_variant h has_arg
    )
)
and type__of_string ?pos s =
  read_type_ (Bi_inbuf.from_string ?pos s)
let rec _2_tag = Bi_io.array_tag
and write_untagged__2 ob x = (
  Atdgen_runtime.Ob_run.write_untagged_list
    expr_tag
    (
      write_untagged_expr
    )
) ob x
and write__2 ob x =
  Bi_io.write_tag ob Bi_io.array_tag;
  write_untagged__2 ob x
and string_of__2 ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write__2 ob x;
  Bi_outbuf.contents ob
and expr_tag = Bi_io.variant_tag
and write_untagged_expr = (
  fun ob x ->
    match x with
      | `EVar x ->
        Bi_outbuf.add_char4 ob '\173' '\221' 'O' '\162';
        (
          write_vname
        ) ob x
      | `EFun x ->
        Bi_outbuf.add_char4 ob '\173' '\209' '<' '\250';
        (
          fun ob x ->
            Bi_io.write_tag ob Bi_io.tuple_tag;
            Bi_vint.write_uvint ob 2;
            (
              let x, _ = x in (
                write_name
              ) ob x
            );
            (
              let _, x = x in (
                write__2
              ) ob x
            );
        ) ob x
)
and write_expr ob x =
  Bi_io.write_tag ob Bi_io.variant_tag;
  write_untagged_expr ob x
and string_of_expr ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_expr ob x;
  Bi_outbuf.contents ob
let rec get__2_reader tag = (
  Atdgen_runtime.Ob_run.get_list_reader (
    get_expr_reader
  )
) tag
and read__2 ib = (
  Atdgen_runtime.Ob_run.read_list (
    get_expr_reader
  )
) ib
and _2_of_string ?pos s =
  read__2 (Bi_inbuf.from_string ?pos s)
and get_expr_reader = (
  fun tag ->
    if tag <> 23 then Atdgen_runtime.Ob_run.read_error () else
      fun ib ->
        Bi_io.read_hashtag ib (fun ib h has_arg ->
          match h, has_arg with
            | 769478562, true -> (`EVar (
                (
                  read_vname
                ) ib
              ))
            | 768687354, true -> (`EFun (
                (
                  fun ib ->
                    if Bi_io.read_tag ib <> 20 then Atdgen_runtime.Ob_run.read_error_at ib;
                    let len = Bi_vint.read_uvint ib in
                    if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
                    let x0 =
                      (
                        read_name
                      ) ib
                    in
                    let x1 =
                      (
                        read__2
                      ) ib
                    in
                    for i = 2 to len - 1 do Bi_io.skip ib done;
                    (x0, x1)
                ) ib
              ))
            | _ -> Atdgen_runtime.Ob_run.unsupported_variant h has_arg
        )
)
and read_expr = (
  fun ib ->
    if Bi_io.read_tag ib <> 23 then Atdgen_runtime.Ob_run.read_error_at ib;
    Bi_io.read_hashtag ib (fun ib h has_arg ->
      match h, has_arg with
        | 769478562, true -> (`EVar (
            (
              read_vname
            ) ib
          ))
        | 768687354, true -> (`EFun (
            (
              fun ib ->
                if Bi_io.read_tag ib <> 20 then Atdgen_runtime.Ob_run.read_error_at ib;
                let len = Bi_vint.read_uvint ib in
                if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
                let x0 =
                  (
                    read_name
                  ) ib
                in
                let x1 =
                  (
                    read__2
                  ) ib
                in
                for i = 2 to len - 1 do Bi_io.skip ib done;
                (x0, x1)
            ) ib
          ))
        | _ -> Atdgen_runtime.Ob_run.unsupported_variant h has_arg
    )
)
and expr_of_string ?pos s =
  read_expr (Bi_inbuf.from_string ?pos s)
let _5_tag = Bi_io.num_variant_tag
let write_untagged__5 = (
  Atdgen_runtime.Ob_run.write_untagged_option (
    write_expr
  )
)
let write__5 ob x =
  Bi_io.write_tag ob Bi_io.num_variant_tag;
  write_untagged__5 ob x
let string_of__5 ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write__5 ob x;
  Bi_outbuf.contents ob
let get__5_reader = (
  fun tag ->
    if tag <> 22 then Atdgen_runtime.Ob_run.read_error () else
      fun ib ->
        match Char.code (Bi_inbuf.read_char ib) with
          | 0 -> None
          | 0x80 ->
            Some (
              (
                read_expr
              )
                ib
            )
          | _ -> Atdgen_runtime.Ob_run.read_error_at ib
)
let read__5 = (
  fun ib ->
    if Bi_io.read_tag ib <> 22 then Atdgen_runtime.Ob_run.read_error_at ib;
    match Char.code (Bi_inbuf.read_char ib) with
      | 0 -> None
      | 0x80 ->
        Some (
          (
            read_expr
          )
            ib
        )
      | _ -> Atdgen_runtime.Ob_run.read_error_at ib
)
let _5_of_string ?pos s =
  read__5 (Bi_inbuf.from_string ?pos s)
let _7_tag = Bi_io.num_variant_tag
let write_untagged__7 = (
  Atdgen_runtime.Ob_run.write_untagged_option (
    fun ob x ->
      Bi_io.write_tag ob Bi_io.tuple_tag;
      Bi_vint.write_uvint ob 2;
      (
        let x, _ = x in (
          write_expr
        ) ob x
      );
      (
        let _, x = x in (
          write_type_
        ) ob x
      );
  )
)
let write__7 ob x =
  Bi_io.write_tag ob Bi_io.num_variant_tag;
  write_untagged__7 ob x
let string_of__7 ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write__7 ob x;
  Bi_outbuf.contents ob
let get__7_reader = (
  fun tag ->
    if tag <> 22 then Atdgen_runtime.Ob_run.read_error () else
      fun ib ->
        match Char.code (Bi_inbuf.read_char ib) with
          | 0 -> None
          | 0x80 ->
            Some (
              (
                fun ib ->
                  if Bi_io.read_tag ib <> 20 then Atdgen_runtime.Ob_run.read_error_at ib;
                  let len = Bi_vint.read_uvint ib in
                  if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
                  let x0 =
                    (
                      read_expr
                    ) ib
                  in
                  let x1 =
                    (
                      read_type_
                    ) ib
                  in
                  for i = 2 to len - 1 do Bi_io.skip ib done;
                  (x0, x1)
              )
                ib
            )
          | _ -> Atdgen_runtime.Ob_run.read_error_at ib
)
let read__7 = (
  fun ib ->
    if Bi_io.read_tag ib <> 22 then Atdgen_runtime.Ob_run.read_error_at ib;
    match Char.code (Bi_inbuf.read_char ib) with
      | 0 -> None
      | 0x80 ->
        Some (
          (
            fun ib ->
              if Bi_io.read_tag ib <> 20 then Atdgen_runtime.Ob_run.read_error_at ib;
              let len = Bi_vint.read_uvint ib in
              if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
              let x0 =
                (
                  read_expr
                ) ib
              in
              let x1 =
                (
                  read_type_
                ) ib
              in
              for i = 2 to len - 1 do Bi_io.skip ib done;
              (x0, x1)
          )
            ib
        )
      | _ -> Atdgen_runtime.Ob_run.read_error_at ib
)
let _7_of_string ?pos s =
  read__7 (Bi_inbuf.from_string ?pos s)
let choice_tag = Bi_io.tuple_tag
let write_untagged_choice = (
  fun ob x ->
    Bi_vint.write_uvint ob 2;
    (
      let x, _ = x in (
        Bi_io.write_svint
      ) ob x
    );
    (
      let _, x = x in (
        write__5
      ) ob x
    );
)
let write_choice ob x =
  Bi_io.write_tag ob Bi_io.tuple_tag;
  write_untagged_choice ob x
let string_of_choice ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_choice ob x;
  Bi_outbuf.contents ob
let get_choice_reader = (
  fun tag ->
    if tag <> 20 then Atdgen_runtime.Ob_run.read_error () else
      fun ib ->
        let len = Bi_vint.read_uvint ib in
        if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
        let x0 =
          (
            Atdgen_runtime.Ob_run.read_int
          ) ib
        in
        let x1 =
          (
            read__5
          ) ib
        in
        for i = 2 to len - 1 do Bi_io.skip ib done;
        (x0, x1)
)
let read_choice = (
  fun ib ->
    if Bi_io.read_tag ib <> 20 then Atdgen_runtime.Ob_run.read_error_at ib;
    let len = Bi_vint.read_uvint ib in
    if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
    let x0 =
      (
        Atdgen_runtime.Ob_run.read_int
      ) ib
    in
    let x1 =
      (
        read__5
      ) ib
    in
    for i = 2 to len - 1 do Bi_io.skip ib done;
    (x0, x1)
)
let choice_of_string ?pos s =
  read_choice (Bi_inbuf.from_string ?pos s)
let _6_tag = Bi_io.array_tag
let write_untagged__6 = (
  Atdgen_runtime.Ob_run.write_untagged_list
    choice_tag
    (
      write_untagged_choice
    )
)
let write__6 ob x =
  Bi_io.write_tag ob Bi_io.array_tag;
  write_untagged__6 ob x
let string_of__6 ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write__6 ob x;
  Bi_outbuf.contents ob
let get__6_reader = (
  Atdgen_runtime.Ob_run.get_list_reader (
    get_choice_reader
  )
)
let read__6 = (
  Atdgen_runtime.Ob_run.read_list (
    get_choice_reader
  )
)
let _6_of_string ?pos s =
  read__6 (Bi_inbuf.from_string ?pos s)
let itrace_tag = Bi_io.array_tag
let write_untagged_itrace = (
  write_untagged__6
)
let write_itrace ob x =
  Bi_io.write_tag ob Bi_io.array_tag;
  write_untagged_itrace ob x
let string_of_itrace ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_itrace ob x;
  Bi_outbuf.contents ob
let get_itrace_reader = (
  get__6_reader
)
let read_itrace = (
  read__6
)
let itrace_of_string ?pos s =
  read_itrace (Bi_inbuf.from_string ?pos s)
let rec _3_tag = Bi_io.array_tag
and write_untagged__3 ob x = (
  Atdgen_runtime.Ob_run.write_untagged_list
    form_tag
    (
      write_untagged_form
    )
) ob x
and write__3 ob x =
  Bi_io.write_tag ob Bi_io.array_tag;
  write_untagged__3 ob x
and string_of__3 ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write__3 ob x;
  Bi_outbuf.contents ob
and form_tag = Bi_io.variant_tag
and write_untagged_form = (
  fun ob x ->
    match x with
      | `FTrue -> Bi_outbuf.add_char4 ob '\005' '\233' 'n' '\180'
      | `FFalse -> Bi_outbuf.add_char4 ob '\011' 'w' '\231' '}'
      | `FPred x ->
        Bi_outbuf.add_char4 ob '\131' 'D' '\134' 'G';
        (
          fun ob x ->
            Bi_io.write_tag ob Bi_io.tuple_tag;
            Bi_vint.write_uvint ob 2;
            (
              let x, _ = x in (
                write_name
              ) ob x
            );
            (
              let _, x = x in (
                write__2
              ) ob x
            );
        ) ob x
      | `FConn x ->
        Bi_outbuf.add_char4 ob '\250' '\170' '\129' 'R';
        (
          fun ob x ->
            Bi_io.write_tag ob Bi_io.tuple_tag;
            Bi_vint.write_uvint ob 2;
            (
              let x, _ = x in (
                write_logcon
              ) ob x
            );
            (
              let _, x = x in (
                write__3
              ) ob x
            );
        ) ob x
      | `FBind x ->
        Bi_outbuf.add_char4 ob '\249' '\252' '\189' '#';
        (
          fun ob x ->
            Bi_io.write_tag ob Bi_io.tuple_tag;
            Bi_vint.write_uvint ob 4;
            (
              let x, _, _, _ = x in (
                write_bkind
              ) ob x
            );
            (
              let _, x, _, _ = x in (
                write_name
              ) ob x
            );
            (
              let _, _, x, _ = x in (
                write_type_
              ) ob x
            );
            (
              let _, _, _, x = x in (
                write_form
              ) ob x
            );
        ) ob x
)
and write_form ob x =
  Bi_io.write_tag ob Bi_io.variant_tag;
  write_untagged_form ob x
and string_of_form ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_form ob x;
  Bi_outbuf.contents ob
let rec get__3_reader tag = (
  Atdgen_runtime.Ob_run.get_list_reader (
    get_form_reader
  )
) tag
and read__3 ib = (
  Atdgen_runtime.Ob_run.read_list (
    get_form_reader
  )
) ib
and _3_of_string ?pos s =
  read__3 (Bi_inbuf.from_string ?pos s)
and get_form_reader = (
  fun tag ->
    if tag <> 23 then Atdgen_runtime.Ob_run.read_error () else
      fun ib ->
        Bi_io.read_hashtag ib (fun ib h has_arg ->
          match h, has_arg with
            | 99184308, false -> `FTrue
            | 192407421, false -> `FFalse
            | 54822471, true -> (`FPred (
                (
                  fun ib ->
                    if Bi_io.read_tag ib <> 20 then Atdgen_runtime.Ob_run.read_error_at ib;
                    let len = Bi_vint.read_uvint ib in
                    if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
                    let x0 =
                      (
                        read_name
                      ) ib
                    in
                    let x1 =
                      (
                        read__2
                      ) ib
                    in
                    for i = 2 to len - 1 do Bi_io.skip ib done;
                    (x0, x1)
                ) ib
              ))
            | -89489070, true -> (`FConn (
                (
                  fun ib ->
                    if Bi_io.read_tag ib <> 20 then Atdgen_runtime.Ob_run.read_error_at ib;
                    let len = Bi_vint.read_uvint ib in
                    if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
                    let x0 =
                      (
                        read_logcon
                      ) ib
                    in
                    let x1 =
                      (
                        read__3
                      ) ib
                    in
                    for i = 2 to len - 1 do Bi_io.skip ib done;
                    (x0, x1)
                ) ib
              ))
            | -100877021, true -> (`FBind (
                (
                  fun ib ->
                    if Bi_io.read_tag ib <> 20 then Atdgen_runtime.Ob_run.read_error_at ib;
                    let len = Bi_vint.read_uvint ib in
                    if len < 4 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1; 2; 3 ];
                    let x0 =
                      (
                        read_bkind
                      ) ib
                    in
                    let x1 =
                      (
                        read_name
                      ) ib
                    in
                    let x2 =
                      (
                        read_type_
                      ) ib
                    in
                    let x3 =
                      (
                        read_form
                      ) ib
                    in
                    for i = 4 to len - 1 do Bi_io.skip ib done;
                    (x0, x1, x2, x3)
                ) ib
              ))
            | _ -> Atdgen_runtime.Ob_run.unsupported_variant h has_arg
        )
)
and read_form = (
  fun ib ->
    if Bi_io.read_tag ib <> 23 then Atdgen_runtime.Ob_run.read_error_at ib;
    Bi_io.read_hashtag ib (fun ib h has_arg ->
      match h, has_arg with
        | 99184308, false -> `FTrue
        | 192407421, false -> `FFalse
        | 54822471, true -> (`FPred (
            (
              fun ib ->
                if Bi_io.read_tag ib <> 20 then Atdgen_runtime.Ob_run.read_error_at ib;
                let len = Bi_vint.read_uvint ib in
                if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
                let x0 =
                  (
                    read_name
                  ) ib
                in
                let x1 =
                  (
                    read__2
                  ) ib
                in
                for i = 2 to len - 1 do Bi_io.skip ib done;
                (x0, x1)
            ) ib
          ))
        | -89489070, true -> (`FConn (
            (
              fun ib ->
                if Bi_io.read_tag ib <> 20 then Atdgen_runtime.Ob_run.read_error_at ib;
                let len = Bi_vint.read_uvint ib in
                if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
                let x0 =
                  (
                    read_logcon
                  ) ib
                in
                let x1 =
                  (
                    read__3
                  ) ib
                in
                for i = 2 to len - 1 do Bi_io.skip ib done;
                (x0, x1)
            ) ib
          ))
        | -100877021, true -> (`FBind (
            (
              fun ib ->
                if Bi_io.read_tag ib <> 20 then Atdgen_runtime.Ob_run.read_error_at ib;
                let len = Bi_vint.read_uvint ib in
                if len < 4 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1; 2; 3 ];
                let x0 =
                  (
                    read_bkind
                  ) ib
                in
                let x1 =
                  (
                    read_name
                  ) ib
                in
                let x2 =
                  (
                    read_type_
                  ) ib
                in
                let x3 =
                  (
                    read_form
                  ) ib
                in
                for i = 4 to len - 1 do Bi_io.skip ib done;
                (x0, x1, x2, x3)
            ) ib
          ))
        | _ -> Atdgen_runtime.Ob_run.unsupported_variant h has_arg
    )
)
and form_of_string ?pos s =
  read_form (Bi_inbuf.from_string ?pos s)
let action_tag = Bi_io.variant_tag
let write_untagged_action = (
  fun ob x ->
    match x with
      | `AId -> Bi_outbuf.add_char4 ob '\000' '1' '\146' '|'
      | `ADef x ->
        Bi_outbuf.add_char4 ob '\171' '*' '\208' '\004';
        (
          fun ob x ->
            Bi_io.write_tag ob Bi_io.tuple_tag;
            Bi_vint.write_uvint ob 2;
            (
              let x, _ = x in (
                fun ob x ->
                  Bi_io.write_tag ob Bi_io.tuple_tag;
                  Bi_vint.write_uvint ob 2;
                  (
                    let x, _ = x in (
                      write_type_
                    ) ob x
                  );
                  (
                    let _, x = x in (
                      write__5
                    ) ob x
                  );
              ) ob x
            );
            (
              let _, x = x in (
                write_uid
              ) ob x
            );
        ) ob x
      | `AIntro x ->
        Bi_outbuf.add_char4 ob '\206' '\128' '\174' 'k';
        (
          fun ob x ->
            Bi_io.write_tag ob Bi_io.tuple_tag;
            Bi_vint.write_uvint ob 2;
            (
              let x, _ = x in (
                Bi_io.write_svint
              ) ob x
            );
            (
              let _, x = x in (
                write__7
              ) ob x
            );
        ) ob x
      | `AElim x ->
        Bi_outbuf.add_char4 ob '\154' '\249' '\188' '\236';
        (
          write_uid
        ) ob x
      | `ACut x ->
        Bi_outbuf.add_char4 ob '\171' '*' '\027' '\193';
        (
          fun ob x ->
            Bi_io.write_tag ob Bi_io.tuple_tag;
            Bi_vint.write_uvint ob 2;
            (
              let x, _ = x in (
                write_form
              ) ob x
            );
            (
              let _, x = x in (
                write_uid
              ) ob x
            );
        ) ob x
      | `AAssume x ->
        Bi_outbuf.add_char4 ob '\143' '\151' '\001' '\141';
        (
          fun ob x ->
            Bi_io.write_tag ob Bi_io.tuple_tag;
            Bi_vint.write_uvint ob 2;
            (
              let x, _ = x in (
                write_form
              ) ob x
            );
            (
              let _, x = x in (
                write_uid
              ) ob x
            );
        ) ob x
      | `AGeneralize x ->
        Bi_outbuf.add_char4 ob '\248' 'D' 'T' '\205';
        (
          write_uid
        ) ob x
      | `AMove x ->
        Bi_outbuf.add_char4 ob '\160' 'E' '\195' '\242';
        (
          fun ob x ->
            Bi_io.write_tag ob Bi_io.tuple_tag;
            Bi_vint.write_uvint ob 2;
            (
              let x, _ = x in (
                write_uid
              ) ob x
            );
            (
              let _, x = x in (
                write__8
              ) ob x
            );
        ) ob x
      | `ADuplicate x ->
        Bi_outbuf.add_char4 ob '\149' '\210' 'q' '\n';
        (
          write_uid
        ) ob x
      | `ALink x ->
        Bi_outbuf.add_char4 ob '\159' '\151' '\248' '\219';
        (
          fun ob x ->
            Bi_io.write_tag ob Bi_io.tuple_tag;
            Bi_vint.write_uvint ob 3;
            (
              let x, _, _ = x in (
                write_ipath
              ) ob x
            );
            (
              let _, x, _ = x in (
                write_ipath
              ) ob x
            );
            (
              let _, _, x = x in (
                write_itrace
              ) ob x
            );
        ) ob x
)
let write_action ob x =
  Bi_io.write_tag ob Bi_io.variant_tag;
  write_untagged_action ob x
let string_of_action ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_action ob x;
  Bi_outbuf.contents ob
let get_action_reader = (
  fun tag ->
    if tag <> 23 then Atdgen_runtime.Ob_run.read_error () else
      fun ib ->
        Bi_io.read_hashtag ib (fun ib h has_arg ->
          match h, has_arg with
            | 3248764, false -> `AId
            | 724226052, true -> (`ADef (
                (
                  fun ib ->
                    if Bi_io.read_tag ib <> 20 then Atdgen_runtime.Ob_run.read_error_at ib;
                    let len = Bi_vint.read_uvint ib in
                    if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
                    let x0 =
                      (
                        fun ib ->
                          if Bi_io.read_tag ib <> 20 then Atdgen_runtime.Ob_run.read_error_at ib;
                          let len = Bi_vint.read_uvint ib in
                          if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
                          let x0 =
                            (
                              read_type_
                            ) ib
                          in
                          let x1 =
                            (
                              read__5
                            ) ib
                          in
                          for i = 2 to len - 1 do Bi_io.skip ib done;
                          (x0, x1)
                      ) ib
                    in
                    let x1 =
                      (
                        read_uid
                      ) ib
                    in
                    for i = 2 to len - 1 do Bi_io.skip ib done;
                    (x0, x1)
                ) ib
              ))
            | -830427541, true -> (`AIntro (
                (
                  fun ib ->
                    if Bi_io.read_tag ib <> 20 then Atdgen_runtime.Ob_run.read_error_at ib;
                    let len = Bi_vint.read_uvint ib in
                    if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
                    let x0 =
                      (
                        Atdgen_runtime.Ob_run.read_int
                      ) ib
                    in
                    let x1 =
                      (
                        read__7
                      ) ib
                    in
                    for i = 2 to len - 1 do Bi_io.skip ib done;
                    (x0, x1)
                ) ib
              ))
            | 452574444, true -> (`AElim (
                (
                  read_uid
                ) ib
              ))
            | 724179905, true -> (`ACut (
                (
                  fun ib ->
                    if Bi_io.read_tag ib <> 20 then Atdgen_runtime.Ob_run.read_error_at ib;
                    let len = Bi_vint.read_uvint ib in
                    if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
                    let x0 =
                      (
                        read_form
                      ) ib
                    in
                    let x1 =
                      (
                        read_uid
                      ) ib
                    in
                    for i = 2 to len - 1 do Bi_io.skip ib done;
                    (x0, x1)
                ) ib
              ))
            | 261554573, true -> (`AAssume (
                (
                  fun ib ->
                    if Bi_io.read_tag ib <> 20 then Atdgen_runtime.Ob_run.read_error_at ib;
                    let len = Bi_vint.read_uvint ib in
                    if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
                    let x0 =
                      (
                        read_form
                      ) ib
                    in
                    let x1 =
                      (
                        read_uid
                      ) ib
                    in
                    for i = 2 to len - 1 do Bi_io.skip ib done;
                    (x0, x1)
                ) ib
              ))
            | -129739571, true -> (`AGeneralize (
                (
                  read_uid
                ) ib
              ))
            | 541443058, true -> (`AMove (
                (
                  fun ib ->
                    if Bi_io.read_tag ib <> 20 then Atdgen_runtime.Ob_run.read_error_at ib;
                    let len = Bi_vint.read_uvint ib in
                    if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
                    let x0 =
                      (
                        read_uid
                      ) ib
                    in
                    let x1 =
                      (
                        read__8
                      ) ib
                    in
                    for i = 2 to len - 1 do Bi_io.skip ib done;
                    (x0, x1)
                ) ib
              ))
            | 366113034, true -> (`ADuplicate (
                (
                  read_uid
                ) ib
              ))
            | 530053339, true -> (`ALink (
                (
                  fun ib ->
                    if Bi_io.read_tag ib <> 20 then Atdgen_runtime.Ob_run.read_error_at ib;
                    let len = Bi_vint.read_uvint ib in
                    if len < 3 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1; 2 ];
                    let x0 =
                      (
                        read_ipath
                      ) ib
                    in
                    let x1 =
                      (
                        read_ipath
                      ) ib
                    in
                    let x2 =
                      (
                        read_itrace
                      ) ib
                    in
                    for i = 3 to len - 1 do Bi_io.skip ib done;
                    (x0, x1, x2)
                ) ib
              ))
            | _ -> Atdgen_runtime.Ob_run.unsupported_variant h has_arg
        )
)
let read_action = (
  fun ib ->
    if Bi_io.read_tag ib <> 23 then Atdgen_runtime.Ob_run.read_error_at ib;
    Bi_io.read_hashtag ib (fun ib h has_arg ->
      match h, has_arg with
        | 3248764, false -> `AId
        | 724226052, true -> (`ADef (
            (
              fun ib ->
                if Bi_io.read_tag ib <> 20 then Atdgen_runtime.Ob_run.read_error_at ib;
                let len = Bi_vint.read_uvint ib in
                if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
                let x0 =
                  (
                    fun ib ->
                      if Bi_io.read_tag ib <> 20 then Atdgen_runtime.Ob_run.read_error_at ib;
                      let len = Bi_vint.read_uvint ib in
                      if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
                      let x0 =
                        (
                          read_type_
                        ) ib
                      in
                      let x1 =
                        (
                          read__5
                        ) ib
                      in
                      for i = 2 to len - 1 do Bi_io.skip ib done;
                      (x0, x1)
                  ) ib
                in
                let x1 =
                  (
                    read_uid
                  ) ib
                in
                for i = 2 to len - 1 do Bi_io.skip ib done;
                (x0, x1)
            ) ib
          ))
        | -830427541, true -> (`AIntro (
            (
              fun ib ->
                if Bi_io.read_tag ib <> 20 then Atdgen_runtime.Ob_run.read_error_at ib;
                let len = Bi_vint.read_uvint ib in
                if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
                let x0 =
                  (
                    Atdgen_runtime.Ob_run.read_int
                  ) ib
                in
                let x1 =
                  (
                    read__7
                  ) ib
                in
                for i = 2 to len - 1 do Bi_io.skip ib done;
                (x0, x1)
            ) ib
          ))
        | 452574444, true -> (`AElim (
            (
              read_uid
            ) ib
          ))
        | 724179905, true -> (`ACut (
            (
              fun ib ->
                if Bi_io.read_tag ib <> 20 then Atdgen_runtime.Ob_run.read_error_at ib;
                let len = Bi_vint.read_uvint ib in
                if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
                let x0 =
                  (
                    read_form
                  ) ib
                in
                let x1 =
                  (
                    read_uid
                  ) ib
                in
                for i = 2 to len - 1 do Bi_io.skip ib done;
                (x0, x1)
            ) ib
          ))
        | 261554573, true -> (`AAssume (
            (
              fun ib ->
                if Bi_io.read_tag ib <> 20 then Atdgen_runtime.Ob_run.read_error_at ib;
                let len = Bi_vint.read_uvint ib in
                if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
                let x0 =
                  (
                    read_form
                  ) ib
                in
                let x1 =
                  (
                    read_uid
                  ) ib
                in
                for i = 2 to len - 1 do Bi_io.skip ib done;
                (x0, x1)
            ) ib
          ))
        | -129739571, true -> (`AGeneralize (
            (
              read_uid
            ) ib
          ))
        | 541443058, true -> (`AMove (
            (
              fun ib ->
                if Bi_io.read_tag ib <> 20 then Atdgen_runtime.Ob_run.read_error_at ib;
                let len = Bi_vint.read_uvint ib in
                if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
                let x0 =
                  (
                    read_uid
                  ) ib
                in
                let x1 =
                  (
                    read__8
                  ) ib
                in
                for i = 2 to len - 1 do Bi_io.skip ib done;
                (x0, x1)
            ) ib
          ))
        | 366113034, true -> (`ADuplicate (
            (
              read_uid
            ) ib
          ))
        | 530053339, true -> (`ALink (
            (
              fun ib ->
                if Bi_io.read_tag ib <> 20 then Atdgen_runtime.Ob_run.read_error_at ib;
                let len = Bi_vint.read_uvint ib in
                if len < 3 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1; 2 ];
                let x0 =
                  (
                    read_ipath
                  ) ib
                in
                let x1 =
                  (
                    read_ipath
                  ) ib
                in
                let x2 =
                  (
                    read_itrace
                  ) ib
                in
                for i = 3 to len - 1 do Bi_io.skip ib done;
                (x0, x1, x2)
            ) ib
          ))
        | _ -> Atdgen_runtime.Ob_run.unsupported_variant h has_arg
    )
)
let action_of_string ?pos s =
  read_action (Bi_inbuf.from_string ?pos s)
let rec _9_tag = Bi_io.array_tag
and write_untagged__9 ob x = (
  Atdgen_runtime.Ob_run.write_untagged_list
    atree_tag
    (
      write_untagged_atree
    )
) ob x
and write__9 ob x =
  Bi_io.write_tag ob Bi_io.array_tag;
  write_untagged__9 ob x
and string_of__9 ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write__9 ob x;
  Bi_outbuf.contents ob
and atree_tag = Bi_io.variant_tag
and write_untagged_atree = (
  fun ob x ->
    match x with
      | `PNode x ->
        Bi_outbuf.add_char4 ob '\195' '\241' '\158' 'r';
        (
          fun ob x ->
            Bi_io.write_tag ob Bi_io.tuple_tag;
            Bi_vint.write_uvint ob 2;
            (
              let x, _ = x in (
                write_action
              ) ob x
            );
            (
              let _, x = x in (
                write__9
              ) ob x
            );
        ) ob x
)
and write_atree ob x =
  Bi_io.write_tag ob Bi_io.variant_tag;
  write_untagged_atree ob x
and string_of_atree ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_atree ob x;
  Bi_outbuf.contents ob
let rec get__9_reader tag = (
  Atdgen_runtime.Ob_run.get_list_reader (
    get_atree_reader
  )
) tag
and read__9 ib = (
  Atdgen_runtime.Ob_run.read_list (
    get_atree_reader
  )
) ib
and _9_of_string ?pos s =
  read__9 (Bi_inbuf.from_string ?pos s)
and get_atree_reader = (
  fun tag ->
    if tag <> 23 then Atdgen_runtime.Ob_run.read_error () else
      fun ib ->
        Bi_io.read_hashtag ib (fun ib h has_arg ->
          match h, has_arg with
            | -1007575438, true -> (`PNode (
                (
                  fun ib ->
                    if Bi_io.read_tag ib <> 20 then Atdgen_runtime.Ob_run.read_error_at ib;
                    let len = Bi_vint.read_uvint ib in
                    if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
                    let x0 =
                      (
                        read_action
                      ) ib
                    in
                    let x1 =
                      (
                        read__9
                      ) ib
                    in
                    for i = 2 to len - 1 do Bi_io.skip ib done;
                    (x0, x1)
                ) ib
              ))
            | _ -> Atdgen_runtime.Ob_run.unsupported_variant h has_arg
        )
)
and read_atree = (
  fun ib ->
    if Bi_io.read_tag ib <> 23 then Atdgen_runtime.Ob_run.read_error_at ib;
    Bi_io.read_hashtag ib (fun ib h has_arg ->
      match h, has_arg with
        | -1007575438, true -> (`PNode (
            (
              fun ib ->
                if Bi_io.read_tag ib <> 20 then Atdgen_runtime.Ob_run.read_error_at ib;
                let len = Bi_vint.read_uvint ib in
                if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
                let x0 =
                  (
                    read_action
                  ) ib
                in
                let x1 =
                  (
                    read__9
                  ) ib
                in
                for i = 2 to len - 1 do Bi_io.skip ib done;
                (x0, x1)
            ) ib
          ))
        | _ -> Atdgen_runtime.Ob_run.unsupported_variant h has_arg
    )
)
and atree_of_string ?pos s =
  read_atree (Bi_inbuf.from_string ?pos s)
let term_tag = Bi_io.variant_tag
let write_untagged_term = (
  fun ob x ->
    match x with
      | `F x ->
        Bi_outbuf.add_char4 ob '\128' '\000' '\000' 'F';
        (
          write_form
        ) ob x
      | `E x ->
        Bi_outbuf.add_char4 ob '\128' '\000' '\000' 'E';
        (
          write_expr
        ) ob x
)
let write_term ob x =
  Bi_io.write_tag ob Bi_io.variant_tag;
  write_untagged_term ob x
let string_of_term ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_term ob x;
  Bi_outbuf.contents ob
let get_term_reader = (
  fun tag ->
    if tag <> 23 then Atdgen_runtime.Ob_run.read_error () else
      fun ib ->
        Bi_io.read_hashtag ib (fun ib h has_arg ->
          match h, has_arg with
            | 70, true -> (`F (
                (
                  read_form
                ) ib
              ))
            | 69, true -> (`E (
                (
                  read_expr
                ) ib
              ))
            | _ -> Atdgen_runtime.Ob_run.unsupported_variant h has_arg
        )
)
let read_term = (
  fun ib ->
    if Bi_io.read_tag ib <> 23 then Atdgen_runtime.Ob_run.read_error_at ib;
    Bi_io.read_hashtag ib (fun ib h has_arg ->
      match h, has_arg with
        | 70, true -> (`F (
            (
              read_form
            ) ib
          ))
        | 69, true -> (`E (
            (
              read_expr
            ) ib
          ))
        | _ -> Atdgen_runtime.Ob_run.unsupported_variant h has_arg
    )
)
let term_of_string ?pos s =
  read_term (Bi_inbuf.from_string ?pos s)
let _1_tag = Bi_io.array_tag
let write_untagged__1 = (
  Atdgen_runtime.Ob_run.write_untagged_list
    type__tag
    (
      write_untagged_type_
    )
)
let write__1 ob x =
  Bi_io.write_tag ob Bi_io.array_tag;
  write_untagged__1 ob x
let string_of__1 ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write__1 ob x;
  Bi_outbuf.contents ob
let get__1_reader = (
  Atdgen_runtime.Ob_run.get_list_reader (
    get_type__reader
  )
)
let read__1 = (
  Atdgen_runtime.Ob_run.read_list (
    get_type__reader
  )
)
let _1_of_string ?pos s =
  read__1 (Bi_inbuf.from_string ?pos s)
let arity_tag = Bi_io.array_tag
let write_untagged_arity = (
  write_untagged__1
)
let write_arity ob x =
  Bi_io.write_tag ob Bi_io.array_tag;
  write_untagged_arity ob x
let string_of_arity ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_arity ob x;
  Bi_outbuf.contents ob
let get_arity_reader = (
  get__1_reader
)
let read_arity = (
  read__1
)
let arity_of_string ?pos s =
  read_arity (Bi_inbuf.from_string ?pos s)
let sig__tag = Bi_io.tuple_tag
let write_untagged_sig_ = (
  fun ob x ->
    Bi_vint.write_uvint ob 2;
    (
      let x, _ = x in (
        write_arity
      ) ob x
    );
    (
      let _, x = x in (
        write_type_
      ) ob x
    );
)
let write_sig_ ob x =
  Bi_io.write_tag ob Bi_io.tuple_tag;
  write_untagged_sig_ ob x
let string_of_sig_ ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_sig_ ob x;
  Bi_outbuf.contents ob
let get_sig__reader = (
  fun tag ->
    if tag <> 20 then Atdgen_runtime.Ob_run.read_error () else
      fun ib ->
        let len = Bi_vint.read_uvint ib in
        if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
        let x0 =
          (
            read_arity
          ) ib
        in
        let x1 =
          (
            read_type_
          ) ib
        in
        for i = 2 to len - 1 do Bi_io.skip ib done;
        (x0, x1)
)
let read_sig_ = (
  fun ib ->
    if Bi_io.read_tag ib <> 20 then Atdgen_runtime.Ob_run.read_error_at ib;
    let len = Bi_vint.read_uvint ib in
    if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
    let x0 =
      (
        read_arity
      ) ib
    in
    let x1 =
      (
        read_type_
      ) ib
    in
    for i = 2 to len - 1 do Bi_io.skip ib done;
    (x0, x1)
)
let sig__of_string ?pos s =
  read_sig_ (Bi_inbuf.from_string ?pos s)
let bvar_tag = Bi_io.tuple_tag
let write_untagged_bvar = (
  fun ob x ->
    Bi_vint.write_uvint ob 2;
    (
      let x, _ = x in (
        write_type_
      ) ob x
    );
    (
      let _, x = x in (
        write__5
      ) ob x
    );
)
let write_bvar ob x =
  Bi_io.write_tag ob Bi_io.tuple_tag;
  write_untagged_bvar ob x
let string_of_bvar ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_bvar ob x;
  Bi_outbuf.contents ob
let get_bvar_reader = (
  fun tag ->
    if tag <> 20 then Atdgen_runtime.Ob_run.read_error () else
      fun ib ->
        let len = Bi_vint.read_uvint ib in
        if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
        let x0 =
          (
            read_type_
          ) ib
        in
        let x1 =
          (
            read__5
          ) ib
        in
        for i = 2 to len - 1 do Bi_io.skip ib done;
        (x0, x1)
)
let read_bvar = (
  fun ib ->
    if Bi_io.read_tag ib <> 20 then Atdgen_runtime.Ob_run.read_error_at ib;
    let len = Bi_vint.read_uvint ib in
    if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
    let x0 =
      (
        read_type_
      ) ib
    in
    let x1 =
      (
        read__5
      ) ib
    in
    for i = 2 to len - 1 do Bi_io.skip ib done;
    (x0, x1)
)
let bvar_of_string ?pos s =
  read_bvar (Bi_inbuf.from_string ?pos s)
let _17_tag = Bi_io.array_tag
let write_untagged__17 = (
  Atdgen_runtime.Ob_run.write_untagged_list
    Bi_io.tuple_tag
    (
      fun ob x ->
        Bi_vint.write_uvint ob 2;
        (
          let x, _ = x in (
            write_vname
          ) ob x
        );
        (
          let _, x = x in (
            write_uid
          ) ob x
        );
    )
)
let write__17 ob x =
  Bi_io.write_tag ob Bi_io.array_tag;
  write_untagged__17 ob x
let string_of__17 ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write__17 ob x;
  Bi_outbuf.contents ob
let get__17_reader = (
  Atdgen_runtime.Ob_run.get_list_reader (
    fun tag ->
      if tag <> 20 then Atdgen_runtime.Ob_run.read_error () else
        fun ib ->
          let len = Bi_vint.read_uvint ib in
          if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
          let x0 =
            (
              read_vname
            ) ib
          in
          let x1 =
            (
              read_uid
            ) ib
          in
          for i = 2 to len - 1 do Bi_io.skip ib done;
          (x0, x1)
  )
)
let read__17 = (
  Atdgen_runtime.Ob_run.read_list (
    fun tag ->
      if tag <> 20 then Atdgen_runtime.Ob_run.read_error () else
        fun ib ->
          let len = Bi_vint.read_uvint ib in
          if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
          let x0 =
            (
              read_vname
            ) ib
          in
          let x1 =
            (
              read_uid
            ) ib
          in
          for i = 2 to len - 1 do Bi_io.skip ib done;
          (x0, x1)
  )
)
let _17_of_string ?pos s =
  read__17 (Bi_inbuf.from_string ?pos s)
let _14_tag = Bi_io.num_variant_tag
let write_untagged__14 = (
  Atdgen_runtime.Ob_run.write_untagged_option (
    write_type_
  )
)
let write__14 ob x =
  Bi_io.write_tag ob Bi_io.num_variant_tag;
  write_untagged__14 ob x
let string_of__14 ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write__14 ob x;
  Bi_outbuf.contents ob
let get__14_reader = (
  fun tag ->
    if tag <> 22 then Atdgen_runtime.Ob_run.read_error () else
      fun ib ->
        match Char.code (Bi_inbuf.read_char ib) with
          | 0 -> None
          | 0x80 ->
            Some (
              (
                read_type_
              )
                ib
            )
          | _ -> Atdgen_runtime.Ob_run.read_error_at ib
)
let read__14 = (
  fun ib ->
    if Bi_io.read_tag ib <> 22 then Atdgen_runtime.Ob_run.read_error_at ib;
    match Char.code (Bi_inbuf.read_char ib) with
      | 0 -> None
      | 0x80 ->
        Some (
          (
            read_type_
          )
            ib
        )
      | _ -> Atdgen_runtime.Ob_run.read_error_at ib
)
let _14_of_string ?pos s =
  read__14 (Bi_inbuf.from_string ?pos s)
let _15_tag = Bi_io.array_tag
let write_untagged__15 = (
  Atdgen_runtime.Ob_run.write_untagged_list
    _14_tag
    (
      write_untagged__14
    )
)
let write__15 ob x =
  Bi_io.write_tag ob Bi_io.array_tag;
  write_untagged__15 ob x
let string_of__15 ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write__15 ob x;
  Bi_outbuf.contents ob
let get__15_reader = (
  Atdgen_runtime.Ob_run.get_list_reader (
    get__14_reader
  )
)
let read__15 = (
  Atdgen_runtime.Ob_run.read_list (
    get__14_reader
  )
)
let _15_of_string ?pos s =
  read__15 (Bi_inbuf.from_string ?pos s)
let _16_tag = Bi_io.array_tag
let write_untagged__16 = (
  Atdgen_runtime.Ob_run.write_untagged_list
    Bi_io.tuple_tag
    (
      fun ob x ->
        Bi_vint.write_uvint ob 2;
        (
          let x, _ = x in (
            write_name
          ) ob x
        );
        (
          let _, x = x in (
            write__15
          ) ob x
        );
    )
)
let write__16 ob x =
  Bi_io.write_tag ob Bi_io.array_tag;
  write_untagged__16 ob x
let string_of__16 ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write__16 ob x;
  Bi_outbuf.contents ob
let get__16_reader = (
  Atdgen_runtime.Ob_run.get_list_reader (
    fun tag ->
      if tag <> 20 then Atdgen_runtime.Ob_run.read_error () else
        fun ib ->
          let len = Bi_vint.read_uvint ib in
          if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
          let x0 =
            (
              read_name
            ) ib
          in
          let x1 =
            (
              read__15
            ) ib
          in
          for i = 2 to len - 1 do Bi_io.skip ib done;
          (x0, x1)
  )
)
let read__16 = (
  Atdgen_runtime.Ob_run.read_list (
    fun tag ->
      if tag <> 20 then Atdgen_runtime.Ob_run.read_error () else
        fun ib ->
          let len = Bi_vint.read_uvint ib in
          if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
          let x0 =
            (
              read_name
            ) ib
          in
          let x1 =
            (
              read__15
            ) ib
          in
          for i = 2 to len - 1 do Bi_io.skip ib done;
          (x0, x1)
  )
)
let _16_of_string ?pos s =
  read__16 (Bi_inbuf.from_string ?pos s)
let _12_tag = Bi_io.array_tag
let write_untagged__12 = (
  Atdgen_runtime.Ob_run.write_untagged_list
    bvar_tag
    (
      write_untagged_bvar
    )
)
let write__12 ob x =
  Bi_io.write_tag ob Bi_io.array_tag;
  write_untagged__12 ob x
let string_of__12 ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write__12 ob x;
  Bi_outbuf.contents ob
let get__12_reader = (
  Atdgen_runtime.Ob_run.get_list_reader (
    get_bvar_reader
  )
)
let read__12 = (
  Atdgen_runtime.Ob_run.read_list (
    get_bvar_reader
  )
)
let _12_of_string ?pos s =
  read__12 (Bi_inbuf.from_string ?pos s)
let _13_tag = Bi_io.array_tag
let write_untagged__13 = (
  Atdgen_runtime.Ob_run.write_untagged_list
    Bi_io.tuple_tag
    (
      fun ob x ->
        Bi_vint.write_uvint ob 2;
        (
          let x, _ = x in (
            write_name
          ) ob x
        );
        (
          let _, x = x in (
            write__12
          ) ob x
        );
    )
)
let write__13 ob x =
  Bi_io.write_tag ob Bi_io.array_tag;
  write_untagged__13 ob x
let string_of__13 ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write__13 ob x;
  Bi_outbuf.contents ob
let get__13_reader = (
  Atdgen_runtime.Ob_run.get_list_reader (
    fun tag ->
      if tag <> 20 then Atdgen_runtime.Ob_run.read_error () else
        fun ib ->
          let len = Bi_vint.read_uvint ib in
          if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
          let x0 =
            (
              read_name
            ) ib
          in
          let x1 =
            (
              read__12
            ) ib
          in
          for i = 2 to len - 1 do Bi_io.skip ib done;
          (x0, x1)
  )
)
let read__13 = (
  Atdgen_runtime.Ob_run.read_list (
    fun tag ->
      if tag <> 20 then Atdgen_runtime.Ob_run.read_error () else
        fun ib ->
          let len = Bi_vint.read_uvint ib in
          if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
          let x0 =
            (
              read_name
            ) ib
          in
          let x1 =
            (
              read__12
            ) ib
          in
          for i = 2 to len - 1 do Bi_io.skip ib done;
          (x0, x1)
  )
)
let _13_of_string ?pos s =
  read__13 (Bi_inbuf.from_string ?pos s)
let _11_tag = Bi_io.array_tag
let write_untagged__11 = (
  Atdgen_runtime.Ob_run.write_untagged_list
    Bi_io.tuple_tag
    (
      fun ob x ->
        Bi_vint.write_uvint ob 2;
        (
          let x, _ = x in (
            write_name
          ) ob x
        );
        (
          let _, x = x in (
            write_sig_
          ) ob x
        );
    )
)
let write__11 ob x =
  Bi_io.write_tag ob Bi_io.array_tag;
  write_untagged__11 ob x
let string_of__11 ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write__11 ob x;
  Bi_outbuf.contents ob
let get__11_reader = (
  Atdgen_runtime.Ob_run.get_list_reader (
    fun tag ->
      if tag <> 20 then Atdgen_runtime.Ob_run.read_error () else
        fun ib ->
          let len = Bi_vint.read_uvint ib in
          if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
          let x0 =
            (
              read_name
            ) ib
          in
          let x1 =
            (
              read_sig_
            ) ib
          in
          for i = 2 to len - 1 do Bi_io.skip ib done;
          (x0, x1)
  )
)
let read__11 = (
  Atdgen_runtime.Ob_run.read_list (
    fun tag ->
      if tag <> 20 then Atdgen_runtime.Ob_run.read_error () else
        fun ib ->
          let len = Bi_vint.read_uvint ib in
          if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
          let x0 =
            (
              read_name
            ) ib
          in
          let x1 =
            (
              read_sig_
            ) ib
          in
          for i = 2 to len - 1 do Bi_io.skip ib done;
          (x0, x1)
  )
)
let _11_of_string ?pos s =
  read__11 (Bi_inbuf.from_string ?pos s)
let _10_tag = Bi_io.array_tag
let write_untagged__10 = (
  Atdgen_runtime.Ob_run.write_untagged_list
    Bi_io.tuple_tag
    (
      fun ob x ->
        Bi_vint.write_uvint ob 2;
        (
          let x, _ = x in (
            write_name
          ) ob x
        );
        (
          let _, x = x in (
            write_arity
          ) ob x
        );
    )
)
let write__10 ob x =
  Bi_io.write_tag ob Bi_io.array_tag;
  write_untagged__10 ob x
let string_of__10 ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write__10 ob x;
  Bi_outbuf.contents ob
let get__10_reader = (
  Atdgen_runtime.Ob_run.get_list_reader (
    fun tag ->
      if tag <> 20 then Atdgen_runtime.Ob_run.read_error () else
        fun ib ->
          let len = Bi_vint.read_uvint ib in
          if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
          let x0 =
            (
              read_name
            ) ib
          in
          let x1 =
            (
              read_arity
            ) ib
          in
          for i = 2 to len - 1 do Bi_io.skip ib done;
          (x0, x1)
  )
)
let read__10 = (
  Atdgen_runtime.Ob_run.read_list (
    fun tag ->
      if tag <> 20 then Atdgen_runtime.Ob_run.read_error () else
        fun ib ->
          let len = Bi_vint.read_uvint ib in
          if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
          let x0 =
            (
              read_name
            ) ib
          in
          let x1 =
            (
              read_arity
            ) ib
          in
          for i = 2 to len - 1 do Bi_io.skip ib done;
          (x0, x1)
  )
)
let _10_of_string ?pos s =
  read__10 (Bi_inbuf.from_string ?pos s)
let env_tag = Bi_io.record_tag
let write_untagged_env : Bi_outbuf.t -> env -> unit = (
  fun ob x ->
    Bi_vint.write_uvint ob 5;
    Bi_outbuf.add_char4 ob '\147' '\162' '\163' '\156';
    (
      write__10
    ) ob x.env_prp;
    Bi_outbuf.add_char4 ob '\147' '\155' '\015' '\173';
    (
      write__11
    ) ob x.env_fun;
    Bi_outbuf.add_char4 ob '\147' '\167' '"' 'U';
    (
      write__13
    ) ob x.env_var;
    Bi_outbuf.add_char4 ob '\157' 'T' '[' '\197';
    (
      write__16
    ) ob x.env_tvar;
    Bi_outbuf.add_char4 ob '\178' '\148' 'B' '9';
    (
      write__17
    ) ob x.env_handles;
)
let write_env ob x =
  Bi_io.write_tag ob Bi_io.record_tag;
  write_untagged_env ob x
let string_of_env ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_env ob x;
  Bi_outbuf.contents ob
let get_env_reader = (
  fun tag ->
    if tag <> 21 then Atdgen_runtime.Ob_run.read_error () else
      fun ib ->
        let field_env_prp = ref (Obj.magic (Sys.opaque_identity 0.0)) in
        let field_env_fun = ref (Obj.magic (Sys.opaque_identity 0.0)) in
        let field_env_var = ref (Obj.magic (Sys.opaque_identity 0.0)) in
        let field_env_tvar = ref (Obj.magic (Sys.opaque_identity 0.0)) in
        let field_env_handles = ref (Obj.magic (Sys.opaque_identity 0.0)) in
        let bits0 = ref 0 in
        let len = Bi_vint.read_uvint ib in
        for i = 1 to len do
          match Bi_io.read_field_hashtag ib with
            | 329425820 ->
              field_env_prp := (
                (
                  read__10
                ) ib
              );
              bits0 := !bits0 lor 0x1;
            | 328929197 ->
              field_env_fun := (
                (
                  read__11
                ) ib
              );
              bits0 := !bits0 lor 0x2;
            | 329720405 ->
              field_env_var := (
                (
                  read__13
                ) ib
              );
              bits0 := !bits0 lor 0x4;
            | 492067781 ->
              field_env_tvar := (
                (
                  read__16
                ) ib
              );
              bits0 := !bits0 lor 0x8;
            | 848577081 ->
              field_env_handles := (
                (
                  read__17
                ) ib
              );
              bits0 := !bits0 lor 0x10;
            | _ -> Bi_io.skip ib
        done;
        if !bits0 <> 0x1f then Atdgen_runtime.Ob_run.missing_fields [| !bits0 |] [| "env_prp"; "env_fun"; "env_var"; "env_tvar"; "env_handles" |];
        (
          {
            env_prp = !field_env_prp;
            env_fun = !field_env_fun;
            env_var = !field_env_var;
            env_tvar = !field_env_tvar;
            env_handles = !field_env_handles;
          }
         : env)
)
let read_env = (
  fun ib ->
    if Bi_io.read_tag ib <> 21 then Atdgen_runtime.Ob_run.read_error_at ib;
    let field_env_prp = ref (Obj.magic (Sys.opaque_identity 0.0)) in
    let field_env_fun = ref (Obj.magic (Sys.opaque_identity 0.0)) in
    let field_env_var = ref (Obj.magic (Sys.opaque_identity 0.0)) in
    let field_env_tvar = ref (Obj.magic (Sys.opaque_identity 0.0)) in
    let field_env_handles = ref (Obj.magic (Sys.opaque_identity 0.0)) in
    let bits0 = ref 0 in
    let len = Bi_vint.read_uvint ib in
    for i = 1 to len do
      match Bi_io.read_field_hashtag ib with
        | 329425820 ->
          field_env_prp := (
            (
              read__10
            ) ib
          );
          bits0 := !bits0 lor 0x1;
        | 328929197 ->
          field_env_fun := (
            (
              read__11
            ) ib
          );
          bits0 := !bits0 lor 0x2;
        | 329720405 ->
          field_env_var := (
            (
              read__13
            ) ib
          );
          bits0 := !bits0 lor 0x4;
        | 492067781 ->
          field_env_tvar := (
            (
              read__16
            ) ib
          );
          bits0 := !bits0 lor 0x8;
        | 848577081 ->
          field_env_handles := (
            (
              read__17
            ) ib
          );
          bits0 := !bits0 lor 0x10;
        | _ -> Bi_io.skip ib
    done;
    if !bits0 <> 0x1f then Atdgen_runtime.Ob_run.missing_fields [| !bits0 |] [| "env_prp"; "env_fun"; "env_var"; "env_tvar"; "env_handles" |];
    (
      {
        env_prp = !field_env_prp;
        env_fun = !field_env_fun;
        env_var = !field_env_var;
        env_tvar = !field_env_tvar;
        env_handles = !field_env_handles;
      }
     : env)
)
let env_of_string ?pos s =
  read_env (Bi_inbuf.from_string ?pos s)
let goal_tag = Bi_io.tuple_tag
let write_untagged_goal = (
  fun ob x ->
    Bi_vint.write_uvint ob 3;
    (
      let x, _, _ = x in (
        write_env
      ) ob x
    );
    (
      let _, x, _ = x in (
        write__3
      ) ob x
    );
    (
      let _, _, x = x in (
        write_form
      ) ob x
    );
)
let write_goal ob x =
  Bi_io.write_tag ob Bi_io.tuple_tag;
  write_untagged_goal ob x
let string_of_goal ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_goal ob x;
  Bi_outbuf.contents ob
let get_goal_reader = (
  fun tag ->
    if tag <> 20 then Atdgen_runtime.Ob_run.read_error () else
      fun ib ->
        let len = Bi_vint.read_uvint ib in
        if len < 3 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1; 2 ];
        let x0 =
          (
            read_env
          ) ib
        in
        let x1 =
          (
            read__3
          ) ib
        in
        let x2 =
          (
            read_form
          ) ib
        in
        for i = 3 to len - 1 do Bi_io.skip ib done;
        (x0, x1, x2)
)
let read_goal = (
  fun ib ->
    if Bi_io.read_tag ib <> 20 then Atdgen_runtime.Ob_run.read_error_at ib;
    let len = Bi_vint.read_uvint ib in
    if len < 3 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1; 2 ];
    let x0 =
      (
        read_env
      ) ib
    in
    let x1 =
      (
        read__3
      ) ib
    in
    let x2 =
      (
        read_form
      ) ib
    in
    for i = 3 to len - 1 do Bi_io.skip ib done;
    (x0, x1, x2)
)
let goal_of_string ?pos s =
  read_goal (Bi_inbuf.from_string ?pos s)
