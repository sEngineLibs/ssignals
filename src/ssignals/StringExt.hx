package ssignals;

using ssignals.StringExt;

class StringExt {
	public static function startsWith(str:String, value:String):Bool {
		return StringTools.startsWith(str, value);
	}

	public static function endsWith(str:String, value:String):Bool {
		return StringTools.endsWith(str, value);
	}

	public static function replace(str:String, sub:String, by:String):String {
		return StringTools.replace(str, sub, by);
	}

	public static function contains(str:String, value:String):Bool {
		return StringTools.contains(str, value);
	}

	public static function trim(str:String):String {
		return StringTools.trim(str);
	}

	public static function capitalize(word:String):String {
		return word.charAt(0).toUpperCase() + word.substr(1);
	}

	public static function capitalizeWords(str:String, delimiter:String = ' '):String {
		return str.split(delimiter).map(capitalize).join(delimiter);
	}

	public static function cleanSpaces(str:String):String {
		return ~/\s+/.replace(str.trim(), " ");
	}

	public static function cleanLines(str:String):String {
		return str.split("\n").filter(line -> line != "").join("\n");
	}

	public static function strip(str:String):String {
		return str.replace('\n', ' ');
	}

	public static function toCharArray(s:String):Array<Int> {
		return [
			for (i in 0...s.length)
				s.charCodeAt(i)
		];
	}
}
