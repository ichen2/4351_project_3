package Semant;

import Absyn.ExpList;
import Absyn.SeqExp;
import ErrorMsg.ErrorMsg;
import Symbol.Table;
import java.util.Hashtable;
import Translate.Exp;
import Types.*;
//import Types.Type;

public class Semant {
  Env env;

  public Semant(ErrorMsg.ErrorMsg err) {
    this(new Env(err));
  }

  Semant(Env e) {
    env = e;  //do I need to make it this.env = e;
  }

  public void transProg(Absyn.Exp exp) {
    transExp(exp);
  }

  private void transArgs(int epos, Types.RECORD formal, Absyn.ExpList args)
  {
  	if(formal == null){
  		if(args != null){
  			error(args.head.pos, "too many arguements!");
  		}
  	}
  	if(args == null){
  		error(epos, "missing argument for " + formal.fieldName);  //where is fieldName

  	}

  	ExpTy e = transExp(args.head);
  	if(!e.ty.coerceTo(formal.fieldType))
  		error(args.head.pos, "argument type mismatch!");
  }

  private void error(int pos, String msg) {
    env.errorMsg.error(pos, msg);   //do i need to make it this.env.errorMsg.error(pos, msg);
  }

  //static final Types.VOID   VOID   = new Types.VOID();   keeping types. to avoid confusion
  static final Types.VOID   VOID   = new VOID();
  static final Types.INT    INT    = new INT();
  static final Types.STRING STRING = new STRING();
  static final TypesNIL    NIL    = new NIL();

  private Exp checkInt(ExpTy et, int pos) {
    if (!INT.coerceTo(et.ty))
      error(pos, "integer required");
    return et.exp;
  }

  private Exp checkComparable(ExpTy et, int pos) //checks to see if it is a valid type
  {
  	Type a = et.ty.actual();
  	if ((!(a instanceof INT)) ||
  		(!(a instanceof STRING)) ||
  		(!(a instanceof NIL)) ||
  		(!(a instanceof RECORD)) ||
  		(!(a instanceof ARRAY)))
  	{
  		error(pos, "integer, string, nil, record, or array is required");
  	}
  	return et.exp;
  }

  private Exp checkOrderable(ExpTy et, int pos)
  {
  	Type a = et.ty.actual();
  	if((!(a instanceof INT)) ||
  		(!(a instanceof STRING)))
  	{
  		error(pos, "integer or string is required");
  	}
  	return et.exp;
  }

  ExpTy transExp(Absyn.Exp e) {
    ExpTy result;

    if (e == null)
      return new ExpTy(null, VOID);
    else if (e instanceof Absyn.OpExp)
      result = transExp((Absyn.OpExp)e);
    else if (e instanceof Absyn.LetExp)
      result = transExp((Absyn.LetExp)e);
    else if (e instanceof Absyn.VarExp)
	    result = transExp((Absyn.VarExp)e);
    else if (e instanceof Absyn.NilExp)
	    result = transExp((Absyn.NilExp)e);
    else if (e instanceof Absyn.IntExp)
	    result = transExp((Absyn.IntExp)e);
    else if (e instanceof Absyn.StringExp)
	    result = transExp((Absyn.StringExp)e);
    else if (e instanceof Absyn.CallExp)
	    result = transExp((Absyn.CallExp)e);
    else if (e instanceof Absyn.RecordExp)
 	    result = transExp((Absyn.RecordExp)e);
    else if (e instanceof Absyn.SeqExp)
	    result = transExp((Absyn.SeqExp)e);
    else if (e instanceof Absyn.AssignExp)
	    result = transExp((Absyn.AssignExp)e);
    else if (e instanceof Absyn.IfExp)
	    result = transExp((Absyn.IfExp)e);
    else if (e instanceof Absyn.WhileExp)
	    result = transExp((Absyn.WhileExp)e);
    else if (e instanceof Absyn.ForExp)
	    result = transExp((Absyn.ForExp)e);
    else if (e instanceof Absyn.BreakExp)
	    result = transExp((Absyn.BreakExp)e);
    else if (e instanceof Absyn.ArrayExp)
	    result = transExp((Absyn.ArrayExp)e);
    else throw new Error("Semant.transExp");
    e.type = result.ty;
    return result;
  }

  private void putTypeFields(Types.RECORD f)
  {
  	if(f == null){
  		return;
  	}
  	env.venv.put(f.fieldName, new VarEntry(f.fieldType));
  	putTypefields(f.tail); //recursion with tail
  }

  ExpTy transExp(Absyn.OpExp e) {
    ExpTy left = transExp(e.left);
    ExpTy right = transExp(e.right);

    switch (e.oper) {
    case Absyn.OpExp.PLUS:
    case Absyn.OpExp.MINUS:
    case Absyn.OpExp.MUL:
    case Absyn.OpExp.DIV:
      checkInt(left, e.left.pos);
      checkInt(right, e.right.pos);
      return new ExpTy(null, INT);
    case Absyn.OpExp.EQ:
    case Absyn.OpExp.NE:
      checkComparable(left, e.left.pos);
      checkComparable(right, e.right.pos);
      if(STRING.coerceTo(left.ty) && STRING.coerceTo(right.ty)) {
        return new ExpTy(null, INT);
      }
      else if(!left.ty.coerceTo(right.ty) && !right.ty.coerceTo(left.ty)) {
        error(e.pos, "Operands not valid for equality");
      }
      return new ExpTy(null, INT);
    case Absyn.OpExp.LT:
    case Absyn.OpExp.LE:
    case Absyn.OpExp.GT:
    case Absyn.OpExp.GE:
      checkComparable(left, e.left.pos);
      checkComparable(right, e.right.pos);
      if(STRING.coerceTo(left.ty) && STRING.coerceTo(right.ty)) {
        return new ExpTy(null, INT);
      }
      else if(!left.ty.coerceTo(right.ty) && !right.ty.coerceTo(left.ty)) {
        error(e.pos, "Operands not valid for inequality");
      }
      return new ExpTy(null, INT);
    default:
      throw new Error("unknown operator");
    }
  }

  ExpTy transExp(Absyn.LetExp e) {
    env.venv.beginScope();
    env.tenv.beginScope();
    for (Absyn.DecList d = e.decs; d != null; d = d.tail) {
      transDec(d.head);
    }
    ExpTy body = transExp(e.body);
    env.venv.endScope();
    env.tenv.endScope();
    return new ExpTy(null, body.ty);
  }

  ExpTy transExp(Absyn.VarExp e) {
    return transVar(e.var);
  }

  ExpTy transExp(Absyn.NilExp e) {
    return new ExpTy(null, NIL);
  }

  ExpTy transExp(Absyn.IntExp e) {
    return new ExpTy(null, INT);
  }

  ExpTy transExp(Absyn.StringExp e) {
    return new ExpTy(null, STRING);
  }

  // skipping CallExp for now

  ExpTy transExp(Absyn.RecordExp e) {
    Types.NAME type = (Types.NAME) env.tenv.get(e.typ);
    if(type != null) {
      Type actual = name.actual();
      if(actual instanceof Types.RECORD) {
        Types.RECORD record = (Types.RECORD) actual;
        if(record == null) {
          error(e.pos, )
        }
        for(Absyn.FieldExpList field = e.fields; field != null; field = field.tail) {
          ExpTy value = transExp(field.init);

          if(record == null) {
            error(e.pos, "too many expressions");
          }
          else if(field.name != record.fieldName) {
            error(field.pos, "field names do not match");
          }
          else if(!value.ty.coerceTo(record.fieldType)) {
            error(field.pos, "field types do not match");
          }
          if(record != null) {
            record = record.tail;
          }
        }
      }
    }
    else {
      error(e.pos, "undeclared type " + e.typ);
    }
    return new ExpTy(null, VOID);
  }

  Exp transDec(Absyn.Dec d) {
    if (d instanceof Absyn.VarDec)
      return transDec((Absyn.VarDec)d);
  	if (d instanceof Absun.FunctionDec)
  		return transDec((Absyn.FunctionDec)d);//need to make a function to handle this
  	if (d instanceof Absyn.TypeDec)
  		return transDec((Absyn.TypeDec)d); //need to make a function to handle this
    throw new Error("Semant.transDec");
  }

  Exp transDec(Absyn.VarDec d) {
    ExpTy init = transExp(d.init);
    Type type;
    if (d.typ == null) {
      if (init.ty.coerceToTo(NIL))
      	error(d.pos, "Record type Missing");	
      type = init.ty;
    } else {
      type = transTy(d.typ);
      if(!init.ty.coerceTo(type))
      	error(d.pos, "Assignment type incompatible");
    }
    d.entry = new VarEntry(type);
    env.venv.put(d.name, d.entry);
    return null;
  }

  Exp transDec(Absyn.FunctionDec d) {  //ian check to see if my hashtables are good
  	Hashtable hash = new Hashtable();
  	for (Absyn.FunctionDec f = d;
  		f != null;
  		f = f.next)
  	{
  		if (hash.put(f.name, f.name) != null)
  			error(f.pos, "function redeclared");
  		Types.RECORD fields = transTypeFields(new Hashtable(), f.params); //need to make this function
  		Type type = transTy(f.result);
  		f.entry = new FunEntry(fields, type);   //helper class
  		env.venv.put(f.name, f.entry);
  	}

  	for (Absyn.FunctionDec f = d;
  		f != null;
  		f = f.next)
  	{
  		env.venv.beginScope();
  		putTypeFields(f.entry.formals);
  		Semant fun = new Semant(env);
  		ExpTy body = fun.transExp(f.body);
  		if(!body.ty.coerceTo(f.entry.result))
  			error(f.body.pos, "result type incompatible");
  		env.venv.endScope();
  	}
  	return null;
  }

  Exp transDec(Absyn.TypeDec d) { //ian can you check my hashtable
  	Hashtable hash = new Hashtable();
  	for(Absyn.TypeDec type = d;
  		type !- null;
  		type = type.next)
  	{
  		if (hash.put(type.name, type.name) != null)
  			error(type.pos, "type redeclared");
  		type.entry = new Types.NAME(type.name);
  		env.tenv.put(type.name, type.entry);
  	}

  	for (Absyn.TypeDec type = d;
  		type != null;
  		type = type.next)
  	{
  		Types.NAME name = (Types.NAME)type.entry;
  		name.bind(transTy(type.ty));
  	}

  	for (Absyn.TypeDec type = d;
  		type != null;
  		type = type.next)
  	{
  		Types.NAME name = (Types.NAME)type.entry;
  		if(name.isLoop()) //where is is loop?  Is it in Types.Name??
  			error(type.pos, "illegal TypeDec");
  	}

  	return null;


  }
}

