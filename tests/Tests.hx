package;

class Tests {
	public static function main() {
		var test = new Test();
		test.onTest(x -> trace(x));
		test.test(1);
		test.test(2);
		test.test(3);
	}
}

@:build(ssignals.Signals.build())
class Test {
	@:signal function test(x:Int);

	public function new() {}
}
