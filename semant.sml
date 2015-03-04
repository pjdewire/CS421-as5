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
  type linkedList = (S.symbol list) ref
  val initVars : linkedList = ref([])

  (*************************************************************************
   *                       UTILITY FUNCTIONS                               *
   *************************************************************************)

  (* checks whether an expression is of type int *)
  fun checkInt ({exp = _, ty = T.INT}, pos) = ()
    | checkInt ({exp = _, ty = _}, pos) = error pos "Must use type int"

  (* prints a type of a varEntry *)
  fun prType (E.VARentry{access=(), ty=T.NIL}) = "NIL"
    | prType (E.VARentry{access=(), ty=T.INT}) = "INT"
    | prType (E.VARentry{access=(), ty=T.STRING}) = "STRING"
    | prType (ty) = "other"

  (* list lookup function: used to prevent assignment to loop variable *)
  fun lookup (key: S.symbol, x::tail) = if x = key then true else lookup (key, tail)
    | lookup (key: S.symbol, nil) = false

  (* prints a type from a type *)
  fun strType (T.NIL) = "NIL"
    | strType (T.INT) = "INT"
    | strType (T.STRING) = "STRING"
    | strType (T.NAME(name, _)) = "T.NAME"
    | strType (T.UNIT) = "UNIT"
    | strType (_) = "OTHER"

  (* finds the base type of a name type *)
    fun baseNameType (T.NAME(sym, ref(SOME(typ)))) = baseNameType(typ)
      | baseNameType (baseType) = baseType

  (* gives type returned by transexp on an exp *)
  fun transexpVal ({exp, ty}) = ty

  (* tests whether types are equal *)
  fun eqType (T.INT, T.INT, _) = true
    | eqType (T.STRING, T.STRING, _) = false
    | eqType (T.UNIT, T.UNIT, _) = false
    | eqType (T.RECORD(l1, u1), T.RECORD(l2, u2), _) = if u1 = u2 then true else
      false
    | eqType (T.RECORD(l1, u1), T.NIL, _) = true
    | eqType (T.NIL, T.RECORD(l1, u1), _) = true
    | eqType (T.ARRAY(t1, u1), T.ARRAY(t2, u2), _) = if u1 = u2 then true else false
    | eqType (t1, t2, _) = if t1 = t2 then true else false

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
  fun checkNeq ({exp=_, ty=T.INT}, {exp=_, ty=T.INT}, pos, _) = (print "top\n"; 
    intRet)
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
    | transty (tenv, A.NameTy(id, pos)) = 
      (case S.look(tenv, id)
      of NONE => (error pos ("Undefined type " ^ S.name(id));
                  (* what type should we return? *)
                  (T.NAME(id, ref(SOME(T.UNIT))), pos))
       | SOME(ty) => (T.NAME(id, ref(SOME(ty))), pos))
    | transty (tenv, _ (* other cases *)) = (* ... *) (T.UNIT, 0)

  (* ...... *)

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
 		   (checkInt (g left, pos);
		    checkInt (g right, pos);
 		    {exp=(), ty=T.INT})

          | g (A.RecordExp {typ,fields,pos}) =
                   (* ... *) {exp=(), ty=T.RECORD ((* ? *) [], ref ())}

          | g (A.StringExp(_, _)) = stringRet()
          | g (A.IntExp(_)) = intRet
          | g (A.NilExp) = nilRet()
          | g (A.SeqExp((exp, pos)::exps)) = (g exp; g(A.SeqExp(exps)))
          | g (A.SeqExp([])) = nilRet()
          | g (A.AssignExp{var, exp, pos}) = 
            (* **************** MAKE SURE NOT A LOOP VAR **************** *)
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
                let val (env', tenv') = transdecs (env, tenv, decs)
                in
                  (* debugging 
                  (case S.look(env', S.symbol("x")) of NONE => print "none trans\n"
                      | SOME(ty) => print("some transexp " ^ prType(ty) ^ "\n"));
                   *) 
                  transexp (env', tenv') body
                end

          | g (A.ArrayExp{typ, size, init, pos}) = 
            (case baseNameType(getOpt(S.look(tenv, typ), T.INT))
              of T.ARRAY(arrtype, u) => if not(arrtype = transexpVal(g(init)))
                then (error pos "Array <type-id> does not match init type";
                      if transexpVal(g(size)) = T.INT then ()
                        else error pos "Size of array must be an int";
                        (* what should we return here? *)
                      intRet)
                else (if transexpVal(g(size)) = T.INT then ()
                        else error pos "Size of array must be an int";
                       {exp=(), ty=T.ARRAY(arrtype, u)})
              | _ => (error pos ("Undefined array type " ^ S.name(typ));
                   (* what should we return here? *)
                   intRet))

          | g (A.IfExp{test, then', else', pos}) =
               (* test must be an integer expression *)
            (if not(baseNameType(transexpVal(g test)) = T.INT)
            (* change this so that evaluate body either way *)
              then error pos "If test must be an integer expression"
              else (); 
              (case else'
                   (* if-then-else. expressions must be of equal type *)
                of SOME(exp) => 
                  if eqTwoExps(g then', g exp, tenv)
                    then {exp=(), ty=transexpVal(g exp)}
                    else (error pos "then and else expressions must of equal type";
                         unRet)
                   (* if-then, no else. expression must produce no value *)
                 | NONE => if (baseNameType(transexpVal(g then')) = T.UNIT)
                   then unRet
                   else (error pos ("if-then expression must produce no value");
                         unRet)))

          | g (A.WhileExp{test, body, pos}) = 
            (if not(baseNameType(transexpVal(g test)) = T.INT)
               then error pos "While test must be an integer expression"
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
                 else (error pos ("For: body of loop must be of type unit, not " ^ strType(baseNameType(transexpVal(transexp (env', tenv') body))));
                   initVars := tl(!initVars); depth := !depth - 1; unRet)
               )
             end
            )
          | g (A.BreakExp(pos)) = if !depth = 0 
             then (error pos "Break must incur within for or while loop"; unRet)
             else unRet

          | g (A.VarExp(var)) = h(var)
          | g _ (* other cases *) = {exp=(), ty=T.INT}

        (* function dealing with "var", may be mutually recursive with g *)
        and h (A.SimpleVar (id,pos)) = (case S.look(env, id)
          of SOME(E.VARentry{access, ty}) => {exp=(), ty=baseNameType(ty)}
          | NONE => (error pos ("Undefined variable " ^ S.name(id));
                     (* what type should this return? *)
                     {exp=(), ty=T.NIL})
          | _ => (error pos ("Cannot use function " ^ S.name(id) ^ " as a variable");
                  (* what type should this return? *)
                  {exp=(), ty=T.NIL}))
	  | h (A.FieldVar (v,id,pos)) = (* ... *) {exp=(), ty=T.INT}
	  | h (A.SubscriptVar (v,exp,pos)) = (* ... *) {exp=(), ty=T.INT}

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
                | SOME(ty) => if baseNameType(expType) = baseNameType(ty)
                                then addVar(env, tenv, name, baseNameType(expType))
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
      
    | transdec (env, tenv, A.FunctionDec(declist)) = (* ... *) (env, tenv)

    | transdec (env, tenv, A.TypeDec({name, ty, pos}::ty_tail)) = 
      let 
        val (transtyRet, pos') = transty(tenv, ty) 
        val tenv' = S.enter(tenv, name, transtyRet)
      in 
        transdec(env, tenv', A.TypeDec(ty_tail))
      end
    | transdec (env, tenv, A.TypeDec(nil)) = (env, tenv)



  (*** transdecs : (E.env * E.tenv * A.dec list) -> (E.env * E.tenv) ***)
  and transdecs (env,tenv,nil) = (env, tenv)
    | transdecs (env,tenv,dec::decs) =
	let val (env',tenv') = transdec (env,tenv,dec)
 	 in transdecs (env',tenv',decs)
	end


  (*** transprog : A.exp -> {exp : ir_code, ty : T.ty} ***)
  fun transprog prog = transexp (E.base_env, E.base_tenv) prog

end  (* structure Semant *)
