
function f(x) {
	var x = g(x);
	return x;
}

function g(y) { 
	return y;
}

var a = f(10);

var b = f(b);