(*
* Peter Dewire
* env.sml
*
* env defines the base environments for the type checker in semant.sml.
* The type environment (base_tenv) contains primitive types INT and STRING.
* The variable/function environment (base_env) contains Tiger's 10 standard 
* library functions
*)

signature ENV =
sig
  type access
  type level
  type label
  type ty

  datatype enventry 
    = VARentry of {access: access, ty: ty}
    | FUNentry of {level: level, label: label, formals: ty list, result: ty}

  type tenv = ty Symbol.table
  type env = enventry Symbol.table

  val base_tenv : tenv
  val base_env : env
end

structure Env : ENV =
struct

  structure S = Symbol
  structure T = Types

  type access = unit   (* not used for the time being *)
  type level = unit    (* not used for the time being *)
  type label = unit    (* not used for the time being *)
  type ty = T.ty

  datatype enventry 
    = VARentry of {access: access, ty: ty}
    | FUNentry of {level: level, label: label, formals: ty list, result: ty}

  type tenv = ty Symbol.table

  type env = enventry Symbol.table

  (* here you need to add all primtive types into the base_tenv *)
  (* primitive types are just int and string *)
  val base_tenv = let
    (* get symbol keys for int and string *)
    val intKey = S.symbol "int";
    val stringKey = S.symbol "string";

    (* build base type environment *)
    val env1 = S.enter(S.empty, intKey, T.INT);
    val env2 = S.enter(env1, stringKey, T.STRING);
    
                  in 
                    env2
                  end
 
  (* here you need to add all primitive library functions into the base_env *)
  val base_env = let
    (* get symbol keys for names of functions *)
    val prKey = S.symbol "print";
    val flKey = S.symbol "flush";
    val gcKey = S.symbol "getchar";
    val orKey = S.symbol "ord";
    val chKey = S.symbol "chr";
    val siKey = S.symbol "size";
    val suKey = S.symbol "substring";
    val coKey = S.symbol "concat";
    val noKey = S.symbol "not";
    val exKey = S.symbol "exit";

    (* build base var/function environment *)
    val env1 = S.enter(S.empty, prKey, FUNentry({level = (), label = (), 
                       formals = T.STRING::nil, result = T.UNIT}));
    val env2 = S.enter(env1, flKey, FUNentry({level = (), label = (), 
                       formals = nil, result = T.UNIT}));
    val env3 = S.enter(env2, gcKey, FUNentry({level = (), label = (), 
                       formals = nil, result = T.STRING}));
    val env4 = S.enter(env3, orKey, FUNentry({level = (), label = (), 
                       formals = T.STRING::nil, result = T.INT}));
    val env5 = S.enter(env4, chKey, FUNentry({level = (), label = (), 
                       formals = T.INT::nil, result = T.STRING}));
    val env6 = S.enter(env5, siKey, FUNentry({level = (), label = (), 
                       formals = T.STRING::nil, result = T.INT}));
    val env7 = S.enter(env6, suKey, FUNentry({level = (), label = (), 
                       formals = T.STRING::T.INT::T.INT::nil, 
                       result = T.STRING}));
    val env8 = S.enter(env7, coKey, FUNentry({level = (), label = (), 
                       formals = T.STRING::T.STRING::nil, result = T.STRING}));
    val env9 = S.enter(env8, noKey, FUNentry({level = (), label = (), 
                       formals = T.INT::nil, result = T.INT}));
    val env10 = S.enter(env9, exKey, FUNentry({level = (), label = (), 
                       formals = T.INT::nil, result = T.UNIT}));

                 in
                   env10
                 end

end  (* structure Env *)
