package ssignals;

#if macro
import haxe.macro.Expr;
import haxe.macro.Context;
import haxe.macro.Type.Ref;
import haxe.macro.TypeTools;
import haxe.macro.ComplexTypeTools;

using haxe.macro.ExprTools;

abstract class Builder {
	static var built:Map<String, {sup:String, fields:Array<Field>}> = [];

	var cls:haxe.macro.Type.ClassType;
	var fields:Array<Field>;
	var newFields:Array<Field>;

	function new() {
		cls = Context.getLocalClass()?.get();
		fields = Context.getBuildFields();
		newFields = [];
	}

	function export() {
		run();
		fields = fields.concat(newFields);
		if (cls != null)
			built.set(cls.name, {
				sup: cls.superClass?.t.get().name,
				fields: fields
			});
		return fields;
	}

	abstract function run():Void;

	function add(field:Field):Field {
		newFields.push(field);
		return field;
	}

	function find(name:String):Field {
		for (field in fields.concat(newFields))
			if (field.name == name)
				return field;
		return null;
	}

	function contains(name:String):Bool {
		return find(name) != null;
	}
}

// SHORTCUTS

function info(msg:String, ?pos:Position) {
	Context.info(msg, pos ?? Context.currentPos());
}

function warn(msg:String, ?pos:Position) {
	Context.warning(msg, pos ?? Context.currentPos());
}

function err(msg:String, ?pos:Position) {
	Context.error(msg, pos ?? Context.currentPos());
}

function fatal(msg:String, ?pos:Position) {
	Context.fatalError(msg, pos ?? Context.currentPos());
}

function fun(args:Array<FunctionArg>, ?ret:ComplexType, ?expr:Expr, ?params:Array<TypeParamDecl>):Function {
	return {
		args: args,
		ret: ret,
		expr: expr,
		params: params
	}
}

function arg(name:String, ?type:ComplexType, ?value:Expr):FunctionArg {
	return {
		name: name,
		type: type,
		value: value
	}
}

function args(v:Array<{name:String, ?type:ComplexType}>) {
	return v.map(a -> arg(a.name, a.type));
}

function anon(fields:Array<Field>):ComplexType {
	return TAnonymous(fields);
}

function def(t:TypeDefinition, ?moduleDependency:String):Void {
	Context.defineType(t, moduleDependency);
}

function tdef(pack:Array<String>, name:String, kind:TypeDefKind, fields:Array<Field>, ?pos:Position, ?doc:String, ?meta:Metadata,
		?params:Array<TypeParamDecl>, ?isExtern:Bool):TypeDefinition {
	return {
		pack: pack,
		name: name,
		kind: kind,
		fields: fields,
		pos: pos ?? Context.currentPos(),
		doc: doc,
		meta: meta,
		params: params,
		isExtern: isExtern
	}
}

function tdEnum(pack:Array<String>, name:String, fields:Array<Field>, ?pos:Position, ?doc:String, ?meta:Metadata, ?params:Array<TypeParamDecl>,
		?isExtern:Bool):TypeDefinition {
	return tdef(pack, name, TDEnum, fields, pos, doc, meta, params);
}

function tdStruct(pack:Array<String>, name:String, fields:Array<Field>, ?pos:Position, ?doc:String, ?meta:Metadata, ?params:Array<TypeParamDecl>,
		?isExtern:Bool):TypeDefinition {
	return tdef(pack, name, TDStructure, fields, pos, doc, meta, params);
}

function tdClass(pack:Array<String>, name:String, fields:Array<Field>, ?superClass:TypePath, ?interfaces:Array<TypePath>, ?isInterface:Bool, ?isFinal:Bool,
		?isAbstract:Bool, ?pos:Position, ?doc:String, ?meta:Metadata, ?params:Array<TypeParamDecl>, ?isExtern:Bool):TypeDefinition {
	return tdef(pack, name, TDClass(superClass, interfaces, isInterface, isFinal, isAbstract), fields, pos, doc, meta, params);
}

function tdAlias(pack:Array<String>, name:String, type:ComplexType, fields:Array<Field>, ?pos:Position, ?doc:String, ?meta:Metadata,
		?params:Array<TypeParamDecl>, ?isExtern:Bool):TypeDefinition {
	return tdef(pack, name, TDAlias(type), fields, pos, doc, meta, params);
}

function tdAbstract(pack:Array<String>, name:String, tthis:Null<ComplexType>, fields:Array<Field>, ?flags:Array<AbstractFlag>, ?from:Array<ComplexType>,
		?to:Array<ComplexType>, ?pos:Position, ?doc:String, ?meta:Metadata, ?params:Array<TypeParamDecl>, ?isExtern:Bool):TypeDefinition {
	return tdef(pack, name, TDAbstract(tthis, flags, from, to), fields, pos, doc, meta, params);
}

function tdField(pack:Array<String>, name:String, kind:FieldType, fields:Array<Field>, ?access:Array<Access>, ?pos:Position, ?doc:String, ?meta:Metadata,
		?params:Array<TypeParamDecl>, ?isExtern:Bool):TypeDefinition {
	return tdef(pack, name, TDField(kind, access), fields, pos, doc, meta, params);
}

function obj(fields:Array<ObjectField>, ?pos:Position):Expr {
	return {
		expr: EObjectDecl(fields),
		pos: pos ?? Context.currentPos()
	}
}

function objField(name:String, ?expr:Expr):ObjectField {
	return {
		field: name,
		expr: expr
	}
}

function meta(name:String, ?params:Array<Expr>, ?pos:Position):MetadataEntry {
	return {
		name: name,
		params: params,
		pos: pos ?? Context.currentPos()
	}
}

function field(name:String, kind:FieldType, ?doc:String, ?access:Array<Access>, ?meta:Metadata, ?pos:Position) {
	return {
		name: name,
		kind: kind,
		doc: doc,
		access: access,
		meta: meta,
		pos: pos ?? Context.currentPos()
	};
}

function variable(name:String, type:ComplexType, ?expr:Expr, ?doc:String, ?access:Array<Access>, ?meta:Metadata, ?pos:Position):Field {
	return field(name, FVar(type, expr), doc, access, meta, pos);
}

function method(name:String, f:Function, ?doc:String, ?access:Array<Access>, ?meta:Metadata, ?pos:Position):Field {
	return field(name, FFun(f), doc, access, meta, pos);
}

function getter(variable:Field, f:Function, ?doc:String, ?access:Array<Access>, ?meta:Metadata, ?pos:Position):Field {
	return switch variable.kind {
		case FProp(get, set, t, e):
			switch get {
				case "get", "null":
					method('get_${variable.name}', f, doc, access, meta, pos);
				default:
					throw 'Can\t add $get getter';
			}
		default: throw 'Can\t add getter to ${variable.kind}';
	}
}

function setter(variable:Field, f:Function, ?doc:String, ?access:Array<Access>, ?meta:Metadata, ?pos:Position):Field {
	return switch variable.kind {
		case FProp(get, set, t, e):
			switch set {
				case "set", "null":
					method('set_${variable.name}', f, doc, access, meta, pos);
				default:
					throw 'Can\t add $set setter';
			}
		default: throw 'Can\t add setter to ${variable.kind}';
	}
}

function toType(type:ComplexType) {
	return ComplexTypeTools.toType(type);
}

function toComplex(type:haxe.macro.Type) {
	return TypeTools.toComplexType(type);
}

function expected(expr:Expr):ComplexType {
	return expr != null ? toComplex(Context.typeof(macro $e{expr})) : macro :Void;
}

function withLocalImports(code:Void->Void) {
	Context.withImports(resolve(Context.getLocalImports()), resolve(Context.getLocalUsing()), () -> {
		code();
	});
}

overload extern inline function resolve(type:ComplexType, ?pos:Position):ComplexType {
	return toComplex(Context.resolveType(type, pos ?? Context.currentPos()));
}

overload extern inline function resolve(imports:Array<ImportExpr>):Array<String> {
	return imports.map(i -> {
		var path = '${i.path.map(p -> p.name).join(".")}';
		switch i.mode {
			case INormal: path;
			case IAsName(alias): '$path as $alias';
			case IAll: '$path.*';
		}
	});
}

overload extern inline function resolve(usings:Array<Ref<haxe.macro.Type.ClassType>>):Array<String> {
	return usings.map(u -> {
		var c = u.get();
		return '${c.pack.join(".")}${c.name}';
	});
}

function copy(v:Field):Field {
	return field(v.name, v.kind, v.doc, v.access, v.meta, v.pos);
}

function eq(a:Expr, b:Expr) {
	return macro $a == $b;
}

function eqChain(a:Array<Expr>, b:Array<Expr>) {
	if (a.length == 1 && b.length == 1)
		return macro ${a[0]} == ${b[0]}
	else
		return macro ${a[0]} == ${b[0]} && ${eqChain(a.slice(1), b.slice(1))};
}

function ident(name:String):Expr {
	var s = name.split(".");
	if (s.length == 1)
		return macro $i{name};
	else
		return macro $p{s};
}

function idents(names:Array<String>) {
	return names.map(name -> ident(name));
}

function traverse(expr:Expr, f:Expr->Expr):Expr {
	return expr.map(e -> f(traverse(e, f)));
}
#end
