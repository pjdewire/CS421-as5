(*
* Peter Dewire
* semant.sml
*
* semant performs type checking for the Tiger language
*)

signature SEMANT =
sig
  type ir_code
  val transprog : Absyn.exp -> {exp: ir_code, ty: Types.ty}
end

structure Semant : SEMANT = 
struct

  structure A = Absyn
  structure E = Env
  structure S = Symbol
  structure T = Types
  val error = ErrorMsg.error
  type ir_code = unit (* not used for the time being *)

  
  (*** FILL IN DETAILS OF YOUR TYPE CHECKER PLEASE !!! ***)

  val depth = ref 0;
  val tempDepth = ref 0;
  type linkedList = (S.symbol list) ref
  val initVars : linkedList = ref([])
  val tempInitVars : linkedList = ref([])
  val tempRet = ref({exp=(), ty=T.UNIT})

  (*************************************************************************
   *                       UTILITY FUNCTIONS                               *
   *************************************************************************)

  (* checks whether an expression is of type int *)
  fun checkInt ({exp = _, ty = T.INT}, {exp=_, ty=T.INT}, pos) = ()
    | checkInt ({exp = _, ty = T.STRING}, {exp=_, ty=T.STRING}, pos) = ()
    | checkInt ({exp = _, ty = _}, {exp=_, ty=_}, pos) = error pos "Must use type int"

  (* returns true if expType is T.RECORD, false otherwise *)
  fun isRecord (T.RECORD(l, u)) = true
    | isRecord (_) = false

  (* list lookup function: used to prevent assignment to loop variable *)
  fun lookup (key: S.symbol, x::tail) = if x = key then true else lookup (key, tail)
    | lookup (key: S.symbol, nil) = false

  (* checks whether there are duplicate fields in a record *)
  fun checkRecordDups ({name, typ, pos}::rec_tail, prevList) = 
    if recLookup(name, prevList) 
      then (error pos "Record cannot have duplicate field names";
        checkRecordDups(rec_tail, name::prevList))
      else checkRecordDups(rec_tail, name::prevList)
    | checkRecordDups (nil, prevList) = ()

  (* searches names that have been parsed so far for duplicates *)
  and recLookup(key: S.symbol, name::name_tail) = 
    if key = name then true else recLookup(key, name_tail)
    | recLookup(key, nil) = false

  (* checks whether a given field is in a record *)
  fun recFind((s1, typ)::rec_tail, key, pos) = if S.name(s1) = S.name(key) then typ else recFind(rec_tail, key, pos)
    | recFind(nil, key, pos) = (error pos "Field not in record"; T.INT)

  (* checks whether there are duplicated paramters in a fundec -- not used *)
  and checkParamDups ({var={name=key, escape=_}, typ=_, pos=pos}::params_tail, prevList) =
      (if recLookup(key, prevList) 
        then error pos "Duplicate paramaters in function declaration"
        else ();
       checkParamDups (params_tail, key::prevList))
    | checkParamDups (nil, prevList) = ()

  (* creates list to allow shadowing *)
  fun shadowList ({var={name, escape}, typ, pos}:: params_tail) = 
      name::shadowList(params_tail)
    | shadowList (nil) = []

  (* creates a ty list for formals in FUNentry *)
  fun formalTyList ({var={name, escape}, typ, pos}::params_tail, tenv, sl) = 
      if not(lookup(name, tl(sl))) then paramLookup(typ, pos, tenv)::formalTyList(params_tail, tenv, tl(sl))
      else paramLookup(typ, pos, tenv)::formalTyList(params_tail, tenv, tl(sl))
    | formalTyList (nil, tenv, sl) = []

  (* looks up paramater type typ in tenv *)
  and paramLookup (typ, pos, tenv) = (case S.look(tenv, typ)
    of NONE => (error pos "Function declaration error: undefined paramter type";
                T.INT)
     | SOME(t) => t)

  (* finds the base type of a name type *)
  fun baseNameType (T.NAME(sym, ref(SOME(typ)))) = baseNameType(typ)
    | baseNameType (baseType) = baseType

   fun detectTypeLoop (tenv, T.NAME(s1, typ), orig) = if orig = s1 
      then true
      (* else detectTypeLoop(tenv, getOpt(typ, T.UNIT), orig) *)
      else (case !typ 
        of SOME(t) => detectTypeLoop(tenv, t, orig)
         | NONE => false)
     | detectTypeLoop (tenv, _, orig) = false

  (* looks up symbol in tenv *)
  fun symLookup (sym, pos, tenv) = 
    (case S.look(tenv, sym)
       of NONE => (error pos "Return type for function undefined"; T.INT)
        | SOME(t) => t)

  (* fills out the empty fields of the return from mutRecursiveEnv *)
  fun setTypes((name,T.NAME(sym, typ))::rec_tail, tenv, pos) = (typ:= S.look(tenv,sym); 
                                                                setTypes(rec_tail, tenv,pos))
    | setTypes((name,ty)::rec_tail, tenv, pos) = setTypes(rec_tail, tenv, pos)
    | setTypes(nil, tenv, pos) = tenv

  (* checks whether there are any empty type fields in the record *)
  fun checkEmptyTypes ((sym, typ)::rec_tail) = (case baseNameType(typ)
    of T.NAME(_, _) => true
     | _ => checkEmptyTypes(rec_tail)
     )
    | checkEmptyTypes (nil) = false

  (* prints a type of a varEntry *)
  fun prType (E.VARentry{access=(), ty=T.NIL}) = "NIL"
    | prType (E.VARentry{access=(), ty=T.INT}) = "INT"
    | prType (E.VARentry{access=(), ty=T.STRING}) = "STRING"
    | prType (ty) = "other"

  (* prints a type from a type *)
  fun strType (T.NIL) = "NIL"
    | strType (T.INT) = "INT"
    | strType (T.STRING) = "STRING"
    | strType (T.NAME(name, _)) = "T.NAME"
    | strType (T.UNIT) = "UNIT"
    | strType (T.RECORD(_,_)) = "RECORD"
    | strType (_) = "OTHER"

  (* gives type returned by transexp on an exp *)
  fun transexpVal ({exp, ty}) = ty

  (* tests whether types are equal *)
  (* always call basename before ? *)
  fun eqType (T.INT, T.INT) = true
    | eqType (T.STRING, T.STRING) = true
    | eqType (T.UNIT, T.UNIT) = true
    | eqType (T.RECORD(l1, u1), T.RECORD(l2, u2)) = if u1 = u2 then true else
      false
    | eqType (T.RECORD(l1, u1), T.NIL) = true
    | eqType (T.NIL, T.RECORD(l1, u1)) = true
    | eqType (T.ARRAY(t1, u1), T.ARRAY(t2, u2)) = if u1 = u2 then true else false
    | eqType (t1, t2) = if t1 = t2 then true else false

  (* returns the symbol of a variable *)
  fun varToSym (var) = case var
    of A.SimpleVar(symbol, _) => symbol
     | A.FieldVar (_, symbol, _) => symbol
     | A.SubscriptVar (var1, _, _) => varToSym(var1)

  (* shortens int type returns *)
  val intRet = {exp=(), ty=T.INT}

  (* shortents unit type returns *)
  val unRet = {exp=(), ty=T.UNIT}

  (* shortens string type returns *)
  fun stringRet () = {exp=(), ty=T.STRING}

  (* shortens string type returns *)
  fun nilRet () = {exp=(), ty=T.NIL}

  (* shortens expression equality tests such as in if-then-else *)
  fun eqTwoExps (e1, e2, tenv) = 
    if baseNameType(transexpVal(e1)) = baseNameType(transexpVal(e2))
      then true
      else false

  (* checks that the types are equal for Neq and Eq (can be ints, arrays or
     records *)
  fun checkNeq ({exp=_, ty=T.INT}, {exp=_, ty=T.INT}, pos, _) = intRet
    | checkNeq ({exp=_, ty=T.STRING}, {exp=_, ty=T.STRING}, pos, _) = intRet
    | checkNeq ({exp=_, ty=T.RECORD(l1, u1)}, {exp=_, ty=T.RECORD(l2, u2)}, 
                pos, _) = if u1 = u2 then intRet
                          else (error pos
                                "Cannot compare records of different types";
                                intRet)
    | checkNeq ({exp=_, ty=T.RECORD(l1, u1)}, {exp=_, ty=T.NIL}, pos, _) =
                intRet
    | checkNeq ({exp=_, ty=T.NIL}, {exp=_, ty=T.RECORD(l1, u1)}, pos, _) =
                intRet
    | checkNeq ({exp=_, ty=T.ARRAY(_, u1)}, {exp=_, ty=T.ARRAY(_, u2)},
                pos, _) = if u1 = u2 then intRet
                          else (error pos
                                "Cannot compare arrays of different types";
                                intRet)
    | checkNeq ({exp=_, ty=_}, {exp=_, ty=_}, pos, tenv) = 
        (error pos "Cannot compare these types with <> or =";
         {exp=(), ty=T.INT})

   (* adds variable with id name and type expType to environment env *)
   fun addVar (env, tenv, name, expType) = 
     let 
       val env' = S.enter(env, name, E.VARentry{access=(), ty=expType})
     in
       (* debugging
       print "in addVar\n";
       (case S.look(env', S.symbol("x")) of NONE => print "none ADDVAR\n"
           | SOME(ventry) => print("SOME ADDVAR " ^ (* prType(ventry) *) ^ " hello\n") );
       *)
       (env', tenv)
     end

   (* adds function to environment env *)
  fun addFunc (env, tenv, name, formals, typ) =
    let
      val env' = S.enter(env, name, E.FUNentry{level=(), label=(), formals=formals, result = typ})
    in
      env'
    end

   (* same as addVar, but returns env' instead of (env', tenv')*)
   fun addVarEnvOnly (env, tenv, name, expType) = 
     let 
       val env' = S.enter(env, name, E.VARentry{access=(), ty=expType})
     in
       env'
     end

   (* returns the (symbol, ty) list of a record, and checks for errors *)
   fun symTyPairList({name, typ, pos}::rec_tail, tenv) =
     (case S.look(tenv, typ)
        of  SOME(fieldType) => (name,
        baseNameType(fieldType))::symTyPairList(rec_tail, tenv)
          | NONE => (error pos "Undefined type in record declaration";
                     (name, T.UNIT)::symTyPairList(rec_tail, tenv)))
     | symTyPairList (nil, tenv) = []

   (* find the length of a a list *)
   fun lstLen(field::fields) = 1 + lstLen(fields)
     | lstLen(nil) = 0

   (* returns a temporary env for use in function declarations *)
   fun funcEnv({name=name1, params=({var={name=name2, escape=_}, typ=typ, pos=p2}::params_tail), 
                result=res, body=body, pos=pos1}, env, tenv) =
       (case S.look(tenv, typ)
         of NONE => (error p2 "Function paramater: undefined type";
              let
                val env' = addVarEnvOnly(env, tenv, name2, T.INT)
              in
                funcEnv({name=name1, params=params_tail, result=res, body=body, pos=pos1}, env', tenv)
              end)
          | SOME(t) => 
              let
                val env' = addVarEnvOnly(env, tenv, name2, t)
              in
                funcEnv({name=name1, params=params_tail, result=res, body=body, pos=pos1}, env', tenv)
              end
       )
     | funcEnv({name=_, params=[], result=_, body=_, pos=_}, env, _) = env


 (**************************************************************************
  *                   TRANSLATING TYPE EXPRESSIONS                         *
  *                                                                        *
  *              transty : (E.tenv * A.ty) -> (T.ty * A.pos)               *
  *************************************************************************)
  fun transty (tenv, A.ArrayTy(id, pos)) = 
      (case S.look(tenv, id)
        of NONE => (error pos ("Undefined type " ^ S.name(id));
                    (* what type of array should we return? *)
                    (T.ARRAY(T.INT, ref ()), pos))
        | SOME(envRet) => (T.ARRAY(envRet, ref ()), pos))
    | transty (tenv, A.RecordTy(nil)) = (T.RECORD(nil, ref ()), 0)
    | transty (tenv, A.RecordTy({name, typ, pos}::rec_tail)) =
      (
       checkRecordDups({name=name, typ=typ, pos=pos}::rec_tail, []);
       (T.RECORD(symTyPairList({name=name, typ=typ, pos=pos}::rec_tail, tenv), ref ()), pos)
      )
    | transty (tenv, A.NameTy(id, pos)) = 
      (case S.look(tenv, id)
      of NONE => (error pos ("Undefined type " ^ S.name(id));
                  (* what type should we return? *)
                  (T.NAME(id, ref(SOME(T.UNIT))), pos))
       | SOME(ty) => (T.NAME(id, ref(SOME(ty))), pos))

 (**************************************************************************
  *                   TRANSLATING EXPRESSIONS                              *
  *                                                                        *
  *  transexp : (E.env * E.tenv) -> (A.exp -> {exp : ir_code, ty : T.ty})  *
  **************************************************************************)
  fun transexp (env, tenv) expr =
    let fun g (A.OpExp {left,oper=A.NeqOp,right,pos}) = 
              (* debugging
              ((case S.look(env, S.symbol("x")) of NONE => print "none OP\n"
                  | SOME(ty) => print("some OP " ^ prType(ty) ^ "\n"));
              *)
              checkNeq(g left, g right, pos, tenv)

          | g (A.OpExp {left,oper=A.EqOp,right,pos}) =
              checkNeq(g left, g right, pos, tenv)

          | g (A.OpExp {left,oper,right,pos}) =
 		   (checkInt (g(left), g(right), pos);
 		    {exp=(), ty=T.INT})

          | g (A.RecordExp {fields, typ, pos}) =
              (case baseNameType(getOpt(S.look(tenv, typ), T.NIL))
                of T.RECORD(l, u) => 
                  if checkEmptyTypes(l) 
                    then transexp (env, setTypes(l, tenv, pos)) expr
                    else
                        (if not(lstLen(fields) = lstLen(l)) 
                          then (error pos "Number of fields in this instantation not equal to type definition";
                                {exp=(), ty=T.INT})
                          else
                            (if checkNames(fields, l, true) then
                               checkEfields(fields, l) else ();
                               {exp=(), ty=T.RECORD(l, u)}))
                               (*
                            if checkEfields(fields, l, true) then {exp=(), ty=T.RECORD(l, u)}
                            else  {exp=(), ty=T.INT})
                            *)
                | _ => (error pos ("Undefined record type " ^ S.name(typ));
                        {exp=(), ty=T.INT}))


          | g (A.StringExp(_, _)) = stringRet()
          | g (A.IntExp(_)) = intRet
          | g (A.NilExp) = nilRet()
          | g (A.SeqExp((exp, pos)::nil)) = g exp
          | g (A.SeqExp((exp, pos)::exps)) = (g exp; g(A.SeqExp(exps)))
          | g (A.SeqExp([])) = unRet
          | g (A.AssignExp{var, exp, pos}) = 
            let 
              val expTyp = baseNameType(transexpVal(g exp))
              val varTyp = baseNameType(transexpVal(h(var)))
            in
              (if expTyp = varTyp then ()
              else error pos "Assignment error: mismatching variable and expression";
              if lookup(varToSym(var), !initVars) then error pos "Assignment error: loop variable may not be assigned to"
              else ();
              {exp=(), ty=T.UNIT})
            end
          | g (A.LetExp{decs, body, pos}) = 
                (
                 (* tempDepth := !depth;
                 depth := 0; *)
                 tempInitVars := !initVars;
                 initVars := [];
                let val (env', tenv') = transdecs (env, tenv, decs)
                in
                  (* depth := !tempDepth; *)
                  tempRet := transexp (env', tenv') body;
                  initVars := !tempInitVars
                end;
                !tempRet)

          | g (A.ArrayExp{typ, size, init, pos}) = 
            (case baseNameType(getOpt(S.look(tenv, typ), T.INT))
              of T.ARRAY(arrtype, u) => 
                let 
                  val initType = baseNameType(transexpVal(g(init)))
                in
                  if (not(baseNameType(arrtype) = initType)
                      andalso not(initType = T.NIL))
                    then (error pos "Array <type-id> does not match init type";
                      if transexpVal(g(size)) = T.INT then ()
                        else error pos "Size of array must be an int";
                        (* what should we return here? Same question below *)
                      intRet)
                    else if transexpVal(g(size)) = T.INT then {exp=(), ty=T.ARRAY(arrtype, u)}
                        else (error pos "Size of array must be an int";
                       (* what to return here -- see piazza *)
                          {exp=(), ty=T.ARRAY(arrtype, u)}) 
                end
              | _ => (error pos ("Undefined array type " ^ S.name(typ));
                   (* what should we return here? *)
                   intRet))

          | g (A.AppExp{func, args, pos}) =
             (case S.look(env, func)
               of NONE => (error pos ("Undefined function " ^ S.name(func)); intRet)
                | SOME(E.VARentry{access, ty}) =>
                    (error pos "Trying to access variable as a function";
                     intRet)
                | SOME(E.FUNentry{level, label, formals, result}) =>
                    (checkParams(formals, args, pos);
                    {exp=(), ty=result}))


          | g (A.IfExp{test, then', else', pos}) =
               (* test must be an integer expression *)
            (if not(baseNameType(transexpVal(g test)) = T.INT)
            (* change this so that evaluate body either way *)
              then error pos "If test must be an integer expression"
              else (); 
              (case else'
                   (* if-then-else. expressions must be of equal type *)
                of SOME(exp) => 
                  if eqTwoExps(g then', g exp, tenv) orelse
                     baseNameType(transexpVal(g(exp))) = T.NIL
                    then {exp=(), ty=transexpVal(g then')}
                    else (error pos "then and else expressions must of equal type";
                         unRet)
                   (* if-then, no else. expression must produce no value *)
                 | NONE => if (baseNameType(transexpVal(g then')) = T.UNIT)
                   then unRet
                   else (error pos ("if-then expression must produce no value");
                         unRet)))

          | g (A.WhileExp{test, body, pos}) = 
            (if not(baseNameType(transexpVal(g test)) = T.INT)
               then error pos ("While test must be an integer expression, not " ^ strType(baseNameType(transexpVal(g test))))
               else ();

             depth := !depth + 1;
             if not(baseNameType(transexpVal(g body)) = T.UNIT)
               then (depth := !depth - 1; unRet)
               else (depth := !depth - 1; unRet)
             )
          | g (A.ForExp{var={name, escape}, lo, hi, body, pos}) = 
            (if ((baseNameType(transexpVal(g lo)) = T.INT) andalso
                 baseNameType(transexpVal(g hi)) = T.INT)
               then ()
               else error pos "For test bounds must be integer expressions";
             let
               val (env', tenv') = addVar(env, tenv, name, transexpVal(g lo))
             in
               (initVars := name :: !initVars;
               depth := !depth + 1;
               if baseNameType(transexpVal(transexp (env', tenv') body)) = T.UNIT
                 then (initVars := tl(!initVars); depth := !depth - 1; unRet)
                 else (error pos ("For: body of loop must be of type unit, not " ^ 
                       strType(baseNameType(transexpVal(transexp (env', tenv') body))));
                   initVars := tl(!initVars); depth := !depth - 1; unRet)
               )
             end
            )
          | g (A.BreakExp(pos)) = if !depth = 0 
             then (error pos "Break must incur within for or while loop"; unRet)
             else unRet

          | g (A.VarExp(var)) = h(var)

        (* function dealing with "var", may be mutually recursive with g *)
        and h (A.SimpleVar (id,pos)) = (case S.look(env, id)
          of SOME(E.VARentry{access, ty}) => {exp=(), ty=baseNameType(ty)}
          | NONE => (error pos ("Undefined variable " ^ S.name(id));
                     (* what type should this return? *)
                     {exp=(), ty=T.INT})
          | _ => (error pos ("Cannot use function " ^ S.name(id) ^ " as a variable");
                  (* what type should this return? *)
                  {exp=(), ty=T.INT}))
	  | h (A.FieldVar (v,id,pos)) = (case h(v)
          of {exp=_, ty=T.RECORD((sym, typ)::rec_tail, _)} =>
             {exp=(), ty=baseNameType(recFind((sym, typ)::rec_tail, id, pos))}
          | _ => (error pos ("Variable " ^ S.name(varToSym(v)) ^ " is not a record");
                  intRet))
	  | h (A.SubscriptVar (v,exp,pos)) = (case h(v)
          of {exp=_, ty=T.ARRAY(typ, u)} =>
            if (baseNameType(transexpVal(g exp))) = T.INT then {exp=(), ty=baseNameType(typ)}
              else (error pos ("Subscript of array variable must be of type INT");
                    intRet)
          | _ => (error pos ("Variable " ^ S.name(varToSym(v)) ^ " is not an array");
          if baseNameType(transexpVal(g exp)) = T.INT then ()
            else error pos ("Subscript of array variable must be of type INT");
          intRet)
        )

      and checkNames ((sym, exp, pos)::rec_tail, (sym2, typ)::dec_tail, retBool) =
        if sym = sym2 then checkNames(rec_tail, dec_tail, retBool)
        else (error pos "Record field names not equal to declaration";
              checkNames(rec_tail, dec_tail, false))
        | checkNames (_, _, flag) = flag

      and checkEfields ((sym, exp, pos)::rec_tail, (sym2, typ):: dec_tail) =
        let
          val expType = baseNameType(transexpVal(g exp))
        in
          if eqType(expType, baseNameType(typ)) 
            then checkEfields (rec_tail, dec_tail)
            else (error pos ("Record instantiation expression not equal to declaration" ^ strType(expType) ^ ", " ^ strType(baseNameType(typ)));
                  checkEfields (rec_tail, dec_tail))
        end
       | checkEfields (nil, nil) = ()
       | checkEfields _ = ()


      (*
      and checkEfields (nil, nil, tBool) = tBool
        | checkEfields ((instName, exp, pos)::inst_tail, (decName, decTy)::dec_tail, tBool) =
        (
          let 
            val retVal = tBool
            val expType = baseNameType(transexpVal(g exp))
          in
            (if (instName = decName) then ()
              else (error pos "Record error: fields out of order";
                    retVal = false;
                    ());
             if (expType = baseNameType(decTy) orelse 
                 (isRecord(expType) andalso baseNameType(decTy) = T.NIL))
               then ()
               else (error pos ("Expression in record instantiation not equal to the type of its id: " ^ strType(expType) ^ ", " ^ strType(decTy));
                     retVal = false;
                     ());
             checkEfields (inst_tail, dec_tail, retVal))
          end
          )
        (* should never reach this case b/c we check length *)
        | checkEfields(_,_,_) = false 
        *)

     and checkParams((typ)::param_tail, (e1)::exps_tail, pos) = 
       if (baseNameType(transexpVal(g e1))) = baseNameType(typ)
          then checkParams(param_tail, exps_tail, pos)
          else (error pos ("Type of function paramater and expression not equal: ");
                checkParams(param_tail, exps_tail, pos))
       | checkParams _ = ()

     in g expr
    end

 (**************************************************************************
  *                   TRANSLATING DECLARATIONS                             *
  *                                                                        *
  *  transdec : (E.env * E.tenv * A.dec) -> (E.env * E.tenv)               *
  **************************************************************************)
  and transdec (env, tenv, A.VarDec{var={name, escape}, typ, init, pos}) = 
      let
        val expType = transexpVal(transexp (env, tenv) init)
      in
          (case typ 
            (* <type> given in "var id : <type> := exp" *)
            of SOME((symbol, pos')) => (case S.look(tenv, symbol)
                (* <type> not in table *)
                of NONE => (error pos ("Undefined type " ^ S.name(symbol)); 
                            addVar(env, tenv, name, baseNameType(expType)))
                | SOME(ty) => if eqType(baseNameType(expType), baseNameType(ty))
                                then addVar(env, tenv, name, ty)
                              else       (* <type> in table but doesn't match *)
                                (error pos ("Initialization " ^ strType(ty) ^ " expression type not equal to constraint type");
                                (* todo: should we add expType or ty? *)
                                addVar(env, tenv, name, baseNameType(expType))))
            (* no <type> given *)
            | NONE => if expType = T.NIL
                        then (error pos "NIL initializations must be constrained by a RECORD type";
                          addVar(env, tenv, name, T.STRING))
                      else addVar(env, tenv, name, baseNameType(expType)))
      end
      
    | transdec (env, tenv, A.FunctionDec({name, params, result, body, pos}::funTails)) =
    (
     tempDepth := !depth;
     depth := 0;
     (* checkParamDups(params, []);*)
     let
       val tempEnv = funcEnv ({name=name, params=params, result=result, body=body,pos=pos}, env, tenv)
       val formals = formalTyList (params, tenv, shadowList(params))
       val expType = transexpVal(transexp (tempEnv, tenv) body)
     in
       (
        depth := !tempDepth;
        (case result
          (* procedure *)
          of NONE => if baseNameType(expType) = T.UNIT
                       then transdec(addFunc(env, tenv, name, formals, T.UNIT), tenv, A.FunctionDec(funTails))
                       else (error pos "Procedure body must return unit";
                       transdec(addFunc(env, tenv, name, formals, T.UNIT), tenv, A.FunctionDec(funTails)))
          (* function *)
           | SOME(sym, p) => 
               if eqType(baseNameType(expType), baseNameType(symLookup(sym, p, tenv)))
               then transdec(addFunc(env, tenv, name, formals, 
                  baseNameType(expType)), tenv, A.FunctionDec(funTails))
               else (error pos "function return type inconsistent with declarations";
                     transdec(addFunc(env, tenv, name, formals,
                  baseNameType(symLookup(sym, p, tenv))), tenv, A.FunctionDec(funTails)))
        )
       )
     end
    )
    | transdec (env, tenv, A.FunctionDec(nil)) = (env, tenv) 

    | transdec (env, tenv, A.TypeDec({name, ty, pos}::ty_tail)) = 
      let 
        val (transtyRet, pos') = transty(tenv, ty) 
        in
          if detectTypeLoop(tenv, transtyRet, name)
            then
              (error pos "Type cycle detected. Type forced to int";
              let
                val tenv' = S.enter(tenv, name, T.INT)
              in
                transdec(env, tenv', A.TypeDec(ty_tail))
              end
              )
            else
              let
                val tenv' = S.enter(tenv, name, transtyRet)
              in
                transdec(env, tenv', A.TypeDec(ty_tail))
              end
        end
        (*
        val tenv' = S.enter(tenv, name, transtyRet)
      in 
        transdec(env, tenv', A.TypeDec(ty_tail))
      end
      *)

    | transdec (env, tenv, A.TypeDec(nil)) = (env, tenv)

  and mutRecursiveEnv (_, _, env, tenv, A.TypeDec(nil)) = (env, tenv)
    | mutRecursiveEnv (_,_, env, tenv, A.VarDec{var, typ, init, pos}) = (env, tenv)
    | mutRecursiveEnv (_, _, env, tenv, A.FunctionDec(nil)) = (env, tenv)
    | mutRecursiveEnv (mutEnv, mutTenv, env, tenv, A.TypeDec({name, ty, pos}::tydec_tail)) =
      ((case S.look(mutTenv, name)
        of NONE => ()
         | SOME(typ) => error pos "Error: you may not redefine types");
        mutRecursiveEnv(mutEnv, S.enter(mutTenv, name, T.NAME(name, ref(NONE))), 
                        env, S.enter(tenv, name, T.NAME(name, ref(NONE))), 
                        A.TypeDec(tydec_tail)))
                        
    | mutRecursiveEnv (mutEnv, mutTenv, env, tenv, A.FunctionDec({name, params,
        result=NONE, body, pos}::funTails)) = 
        ((case S.look(mutEnv, name)
          of NONE => ()
           | SOME(typ) => error pos "Error: you may not redefine procedures");
         let
           val temp =  E.FUNentry{level=(), label=(), formals=formalTyList(params, 
                     tenv, shadowList(params)), result=T.UNIT}
         in
           mutRecursiveEnv(S.enter(mutEnv, name, temp), mutTenv, S.enter(env,
           name, temp), tenv, A.FunctionDec(funTails))
         end
         )
      | mutRecursiveEnv (mutEnv, mutTenv, env, tenv, A.FunctionDec({name, params,
          result=SOME((sym1, p2)), body, pos}::funTails)) = 
          ((case S.look(mutEnv, name)
            of NONE => ()
             | SOME(typ) => error pos "Error: you may not redefine functions");
          let
            val temp = E.FUNentry{level=(), label=(),
            formals=formalTyList(params, tenv, shadowList(params)),
            result=symLookup(sym1, p2, tenv)}
          in
            mutRecursiveEnv(S.enter(mutEnv, name, temp), mutTenv, S.enter(env,
            name, temp), tenv, A.FunctionDec(funTails))
          end
          )

  (*** transdecs : (E.env * E.tenv * A.dec list) -> (E.env * E.tenv) ***)
  and transdecs (env,tenv,nil) = (env, tenv)
    | transdecs (env,tenv,dec::decs) =
	let val (rEnv, rTenv) = mutRecursiveEnv (S.empty, S.empty, env, tenv, dec);
      val (env',tenv') = transdec (rEnv,rTenv,dec)
 	 in transdecs (env',tenv',decs)
	end


  (*** transprog : A.exp -> {exp : ir_code, ty : T.ty} ***)
  fun transprog prog = transexp (E.base_env, E.base_tenv) prog

end  (* structure Semant *)
