package ssignals;

#if macro
import ssignals.Builder;
import haxe.macro.Expr;
import haxe.macro.Context;

using ssignals.Builder;
using ssignals.StringExt;
using haxe.macro.ExprTools;
using haxe.macro.ComplexTypeTools;

class Signals extends Builder {
	static var signalsTypes:Map<String, Array<{name:String, args:Array<FunctionArg>}>> = [];
	static var slotsSignals:Map<String, Map<String, Position>>;

	macro public static function build():Array<Field> {
		return new Signals().export();
	}

	function run() {
		slotsSignals = [];
		if (cls != null)
			signalsTypes.set(cls.name, []);

		for (field in fields) {
			for (meta in field.meta ?? []) {
				switch meta.name {
					case ":inject":
						var injections:Map<String, Function> = [];
						for (slotIdent in extractMetaParams(meta).keyValueIterator()) {
							var slot = find(slotIdent.key);
							if (slot != null) {
								switch slot.kind {
									case FFun(f):
										injections.set(slot.name, f);
									default:
										err('Slot ${slotIdent.key} must be function', slotIdent.value);
								}
							} else
								err('Can\'t find slot ${slotIdent.key}', slotIdent.value);
						}
						buildInjection(field, injections);
					case ":slot":
						slotsSignals.set(field.name, extractMetaParams(meta));

					default:
						if (meta.name.startsWith("track")) {
							var ms = meta.name.split(".");
							buildTrack(field, ms.contains("public"), ms.contains("single"));
						} else if (meta.name.startsWith(":signal")) {
							var ms = meta.name.split(".");
							buildSignal(field, !ms.contains("private"), field.access.contains(AStatic), ms.contains("single"), [
								for (param in extractMetaParams(meta).keys())
									param
							]);
						}
				}
			}
		}

		if (slotsSignals.keys().hasNext()) {
			var constructor = find("new");
			if (constructor == null)
				err("This class must have a constructor");

			var cf = switch constructor.kind {
				case FFun(f): f;
				default: null;
			}

			for (slot in slotsSignals.keyValueIterator()) {
				var conns = [
					for (signal in slot.value.keys()) {
						var p = signal.split(".");
						p[p.length - 1] = 'on${p[p.length - 1].capitalize()}';
						if (p.length == 1) {
							macro $i{p[0]}($i{slot.key});
						} else {
							macro $p{p}($i{slot.key});
						}
					}
				];
				cf.expr = switch cf.expr.expr {
					case EBlock(exprs): macro $b{exprs.concat(conns)};
					default: macro $b{[macro ${cf.expr}].concat(conns)};
				}
			}
		}
	}

	function buildSignal(field:Field, isPublic:Bool, isStatic:Bool, isSingle:Bool, mask:Array<String>):Void {
		if (isSingle)
			buildSingleSignal(field, isPublic, isStatic);
		else
			switch (field.kind) {
				case FFun(f):
					if (f.expr != null)
						warn("This expression will never be used.", f.expr.pos);

					var sArgs = [];
					var sKeys = [];
					for (arg in f.args) {
						arg.type = resolve(arg.type);
						if (mask.contains(arg.name))
							sKeys.push(arg);
						else
							sArgs.push(arg);
					}

					// define underlying type
					var _t_args = [
						for (arg in sArgs) {
							var t = TNamed(arg.name, arg.type);
							if (arg.opt) TOptional(t) else t;
						}
					];
					var _t = ComplexType.TFunction(_t_args, macro :Void);

					signalsTypes.get(cls.name).push({
						name: field.name,
						args: sArgs
					});

					var typeName = '${cls.name}_${field.name}_Signal';
					var stypepath = {
						pack: cls.pack,
						name: typeName,
						params: [
							for (param in cls.params)
								TPType(toComplex(param.t))
						]
					};
					if (sKeys.length == 0) {
						Context.defineType(tdAbstract(cls.pack, typeName, macro :Array<$_t>, [
							method("emit", fun(f.args, macro :Void, macro {
								for (slot in this)
									slot(${
										for (arg in f.args)
											macro $i{arg.name}
									});
							}),
								[APublic, AInline], [meta(":op", [macro a()])]),
							method("connect", fun([arg("slot", _t), arg("keep", macro :Bool, macro true)], macro :Void,
								macro {
									if (keep)
										this.push(slot);
									else {
										${
											{
												expr: EFunction(FNamed("_slot"), {
													args: f.args,
													ret: macro :Void,
													expr: macro {
														slot(${
															for (arg in f.args)
																macro $i{arg.name}
														});
														disconnect(_slot);
													}
												}),
												pos: Context.currentPos()
											}
										};
										this.push(_slot);
									}
								}),
								[APublic, AInline]),
							method("disconnect", fun([arg("slot", _t)], macro :Void, macro this.remove(slot)), [APublic, AInline]),
							method("clear", fun([], macro :Void, macro this = new $stypepath()), [APublic, AInline])
						],
							[AbFrom(macro :Array<$_t>), AbTo(macro :Array<$_t>)], [meta(":forward.new"), meta(":dox", [macro hide])], cls.params.map(p -> {
								name: p.name,
								defaultType: p.defaultType != null ? toComplex(p.defaultType) : null,
								constraints: null,
								params: null,
								meta: null
							}), true));
						// docs
						var paramDoc = "";
						var callDoc = "";
						for (arg in f.args) {
							paramDoc += '${arg.name}:${switch arg.type {
							case TPath(p): p.sub ?? p.name;
							default: 'Void';
						}}, ';
							callDoc += '${arg.name}, ';
						}
						paramDoc = '`${paramDoc.substring(0, paramDoc.length - 2)}`' + (f.args.length == 1 ? " parameter" : " parameters");
						callDoc = '${callDoc.substring(0, callDoc.length - 2)}';
						field.doc = '
							This signal invokes its slots ${f.args.length > 0 ? 'with $paramDoc' : ""} when emitted.
							Call `${field.name}($callDoc)` or `${field.name}.emit($callDoc)` to emit the signal
						';
						field.kind = FVar(TPath(stypepath), macro new $stypepath());
						field.access = [isPublic ? APublic : APrivate];
						if (isStatic)
							field.access.push(AStatic);

						// add connector
						var connector = method('on${field.name.capitalize()}', fun([arg("slot", _t), arg("keep", macro :Bool, macro true)], macro {
							$i{field.name}.connect(slot, keep);
						}), [APublic, AInline]);
						if (isStatic)
							connector.access.push(AStatic);
						connector.doc = '
							Shortcut for `${field.name}` signal\'s function `connect` which connects slots to it.
							@param slot a callback to invoke when `${field.name}` is emitted
						';
						add(connector);
					}
					// masked signal
					else {
						var _m = anon(sKeys.map(k -> variable(k.name, k.type)));
						var underlying = macro :Map<$_m, Array<$_t>>;
						var sidents = sKeys.map(k -> k.name);
						var sidentsExpr = idents(sidents);
						var cond = eqChain(idents([
							for (k in sidents)
								'p.key.$k'
						]), sidentsExpr);
						var stypepath = {
							pack: cls.pack,
							name: typeName,
							params: [
								for (param in cls.params)
									TPType(toComplex(param.t))
							]
						};
						Context.defineType(tdAbstract(cls.pack, typeName, underlying, [
							method("emit", fun(f.args, macro :Void,
								macro {
									for (p in this.keyValueIterator()) {
										if ($cond) {
											for (slot in p.value) {
												slot(${
													for (arg in sArgs)
														macro $i{arg.name}
												});
												break;
											}
										}
									}
								}),
								[APublic, AInline], [meta(":op", [macro a()])]),
							method("connect", fun(args(sKeys).concat([arg("slot", _t), arg("keep", macro :Bool, macro true)]), macro :Void, macro {
								var flag = false;
								for (p in this.keyValueIterator())
									if ($cond) {
										p.value.push(slot);
										flag = true;
										break;
									}
								if (!flag)
									this.set(${
										obj([
											for (k in sKeys)
												objField(k.name, macro $i{k.name})
										])
									}, [slot]);
							}), [APublic, AInline]),
							method("disconnect", fun([arg("slot", _t)], macro :Void,
								macro {
									for (slotList in this)
										if (slotList.contains(slot)) {
											slotList.remove(slot);
											break;
										}
								}),
								[APublic, AInline]),
							method("clear", fun([], macro :Void, macro this = new $stypepath()), [APublic, AInline])
						], [AbFrom(underlying), AbTo(underlying)],
							[meta(":forward.new"), meta(":dox", [macro hide])], cls.params.map(p -> {
								name: p.name,
								defaultType: p.defaultType != null ? toComplex(p.defaultType) : null,
								constraints: null,
								params: null,
								meta: null
							}), true));
						// docs
						var maskValuesDoc = "";
						for (key in sKeys)
							maskValuesDoc += '`${key.name}:${key.type.toString()}`';
						var callDoc = "";
						for (arg in f.args)
							callDoc += '${arg.name}, ';
						callDoc = '${callDoc.substring(0, callDoc.length - 2)}';
						field.doc = '
					When this signal is emitted, only the slots with the exact parameter mask
					($maskValuesDoc) values are invoked.
					Call `${field.name}($callDoc)` or `${field.name}.emit($callDoc)` to emit the signal
					';
						field.kind = FVar(TPath(stypepath), macro new $stypepath());
						field.access = isPublic ? [APublic] : [APrivate];
						if (isStatic)
							field.access.push(AStatic);

						// add connector
						var cargs = sidentsExpr.concat([macro slot, macro keep]);
						var connector = method('on${field.name.capitalize()}',
							fun(args(sKeys).concat([arg("slot", _t), arg("keep", macro :Bool, macro true)]), macro {
								$i{field.name}.connect($a{cargs});
							}), [APublic, AInline]);
						if (isStatic)
							connector.access.push(AStatic);
						var maskDoc = "";
						for (key in sKeys)
							maskDoc += '\n@param ${key.name} Mask parameter of the slot';
						connector.doc = '
					Shortcut for `${field.name}` signal\'s function `connect` which connects slots to it.
					$maskDoc
					@param slot a callback to invoke when `${field.name}` is emitted
					';
						add(connector);
					}

					// add disconnector
					var disconnector = method('off${field.name.capitalize()}', fun([arg("slot", _t)], macro {
						$i{field.name}.disconnect(slot);
					}), [APublic, AInline]);
					if (isStatic)
						disconnector.access.push(AStatic);
					disconnector.doc = '
					Shortcut for `${field.name}` signal\'s function `disconnect` which disconnects slots from it.
					@param slot a callback to remove from `${field.name}`\'s list
					';
					add(disconnector);
				default:
					err("Signal must be declared as a function. Use `track` meta to track this field", field.pos);
			}
	}

	function buildSingleSignal(field:Field, isPublic:Bool, isStatic:Bool):Void {
		switch (field.kind) {
			case FFun(f):
				if (f.expr == null)
					f.expr = macro {};

				field.access = [ADynamic, isPublic ? APublic : APrivate];
				if (isStatic)
					field.access.push(AStatic);

				var connector = method('on${field.name.capitalize()}', fun([arg("slot")], macro {
					$i{field.name} = slot;
				}), [APublic, AInline]);
				if (isStatic)
					connector.access.push(AStatic);
				connector.doc = '
					Shortcut for `${field.name}` signal\'s function `connect` which connects slots to it.
					@param slot a callback to invoke when `${field.name}` is emitted
					';
				add(connector);

				// add disconnector
				var disconnector = method('off${field.name.capitalize()}', fun([arg("slot")], macro {
					$i{field.name} = null;
				}), [APublic, AInline]);
				if (isStatic)
					disconnector.access.push(AStatic);
				disconnector.doc = '
				Shortcut for `${field.name}` signal\'s function `disconnect` which disconnects slots from it.
				@param slot a callback to remove from `${field.name}`\'s list
				';
				add(disconnector);
			default:
				err("Signal must be declared as a function. Use `track` meta to track this field", field.pos);
		}
	}

	function buildTrack(field:Field, isPublic:Bool, isSingle:Bool):Void {
		switch (field.kind) {
			case FVar(t, e):
				field.meta.push(meta(":isVar"));
				field.kind = FProp("default", "set", t, e);
				buildTrack(field, isPublic, isSingle);
			case FProp(get, set, t, e):
				switch set {
					case "set", "null":
						var _setter = find('set_${field.name}');
						if (_setter == null) {
							add(setter(field, {
								args: [arg("value", t)],
								expr: macro {
									$i{field.name} = value;
									return $i{field.name};
								}
							}));
							buildTrack(field, isPublic, isSingle);
						} else {
							switch _setter.kind {
								case FFun(f):
									var signalName = '${field.name}Changed';
									var signal = add(method(signalName, fun([arg(field.name, t)])));
									buildSignal(signal, isPublic, field.access.contains(AStatic), isSingle, []);
									f.expr = macro {
										var __previous__ = $i{field.name};
										${
											inject(f.expr, macro {
												if ($i{field.name} != __previous__)
													$i{signalName}(__previous__);
											})
										};
									}
									field.doc = '_This property is **tracked**. Whenever the property changes, the previous value of it is emitted on connected `$signalName` slots. 
									The corresponding connector is_ `on${signalName.capitalize()}`\n\n'
										+ (field.doc ?? "");
								default: err("Setter must be function", _setter.pos);
							}
						}
					default: err('Can\'t track property with `$set` set access', field.pos);
				}
			case FFun(f):
				var signalName = '${field.name}Called';
				var signalFun = fun(switch (f.ret) {
					case TPath(p):
						p.name == "Void" ? [] : [arg("value", f.ret)];
					default: [arg("value", f.ret)];
				});
				buildInjection(field, [signalName => signalFun]);
				field.doc = '_This function is **tracked**. The result of every function invocation is emitted on connected `$signalName` slots. 
					The corresponding connector is_ `on${signalName.capitalize()}`\n\n'
					+ (field.doc ?? "");
		}
	}

	static function inject(expr1:Expr, expr2:Expr):Expr {
		var injected = false;
		var e = traverse(expr1, e -> switch e.expr {
			case EReturn(e):
				injected = true;
				// if (e != null) macro {
				// 	final __result__ = $e;
				// 	${expr2};
				// 	return __result__;
				// } else
				macro {
					${expr2};
					return $e;
				}
			default: e;
		});
		if (!injected)
			e = macro {
				$e;
				${expr2};
			}
		return e;
	}

	function buildInjection(field:Field, injections:Map<String, Function>) {
		function injectCalls(f:Function, injections:Map<String, Function>) {
			var injected = false;
			if (f.ret != null && f?.ret.toString() != "Void") {
				var block = [];
				for (func in injections.keyValueIterator()) {
					if (func.value.args.length == 0)
						block.push(macro $i{func.key}());
					else
						err('Invalid number of arguments. Expected 0, got ${func.value.args.length}', find(func.key).pos);
				}

				f.expr = macro {
					${f.expr};
					$b{block}
				}
			} else {
				var block = [];
				for (func in injections.keyValueIterator()) {
					var args = func.value.args;
					if (args.length == 0)
						block.push(macro $i{func.key}());
					else if (args.length == 1)
						block.push(macro $i{func.key}(res));
					else
						err('Invalid number of arguments. Expected 1, got ${args.length}', find(func.key).pos);
				}

				f.expr = inject(f.expr, macro $b{block});
			}
		}

		switch field.kind {
			case FVar(t, e):
				field.meta.push(meta(":isVar"));
				field.kind = FProp("default", "set", t, e);
				buildInjection(field, injections);

			case FProp(get, set, t, e):
				switch (set) {
					case "set", "null":
						var _setter = find('set_${field.name}');
						if (_setter == null) {
							// generate setter
							_setter = add(setter(field, fun([arg("value", t)], macro {
								$i{field.name} = value;
								return $i{field.name};
							}), [APrivate, AInline]));
						}
						buildInjection(_setter, injections);

					default:
						err("Can't track property with no write access", field.pos);
				}

			case FFun(f):
				injectCalls(f, injections);
		}
	}

	function extractMetaParams(meta:MetadataEntry):Map<String, Position> {
		function parseField(expr:Expr):String {
			return switch expr.expr {
				case EConst(c):
					switch c {
						case CIdent(s):
							s;
						default:
							err("Identifier expected", expr.pos);
							null;
					}
				case EField(e, field, kind):
					parseField(e) + "." + field;
				default:
					err("Identifier expected", expr.pos);
					null;
			}
		}
		var params:Map<String, Position> = [
			for (param in meta.params ?? [])
				parseField(param) => param.pos
		];
		return params;
	}
}
#end
