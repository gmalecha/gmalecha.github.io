// Copyright (c) 2010 Gregory Malecha
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in
// all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
// THE SOFTWARE.
//
var curves = (function(){
function copyArray(a) {
  var result = new Array();
  for( var i = 0; i < a.length; i++ )
    result.push(a[i]);
  return result;
}

function compileLine(pts) {
  var res = "";
  for(var i = 0; i < pts.length; i++ ) {
    res += " L" + pts[i].x + "," + pts[i].y ;
  }
  return res.substr(1);  
}

function compileBez(translate, _pts) {
  if( _pts.length < 4 )
    return LineCurve(_pts);

  var ary = new Array();
  var pts = copyArray(_pts);
  pts.reverse();

  ary.push(pts[0]);
  ary.push(pts.pop());
  ary.push(pts.pop());
  //ary.push(pts.pop());

  var res = "";
  var started = false;
  do {
    ary.push(pts.pop());
    var bez = translate(ary);
    if( !started ) {
      res = "L" + bez[0].x + "," + bez[0].y + " ";
      started = true;
    }
    res += "C" + bez[1].x + "," + bez[1].y + " " + bez[2].x + "," + bez[2].y + " " + bez[3].x + "," + bez[3].y + " ";
    ary = ary.slice(1, 4);
  } while( pts.length > 0 );

  res += " L" + ary[ary.length-1].x + "," + ary[ary.length-1].y;

  return res;
}

function compileBspline(pts) {
  function bspToBez(pts) {
    var r = new Array();

    r.push(new Pt(1. / 6 * pts[0].x + 2. / 3 * pts[1].x + 1. / 6 * pts[2].x, 1. / 6 * pts[0].y + 2. / 3 * pts[1].y + 1. / 6 * pts[2].y));
    r.push(new Pt(2. / 3 * pts[1].x + 1. / 3 * pts[2].x, 2. / 3 * pts[1].y + 1. / 3 * pts[2].y));
    r.push(new Pt(2. / 3 * pts[2].x + 1. / 3 * pts[1].x, 2. / 3 * pts[2].y + 1. / 3 * pts[1].y));
    r.push(new Pt(1. / 6 * pts[1].x + 2. / 3 * pts[2].x + 1. / 6 * pts[3].x, 1. / 6 * pts[1].y + 2. / 3 * pts[2].y + 1. / 6 * pts[3].y));

    return r;
  }

  return compileBez(bspToBez, pts);
}

function compileCatmullRom(pts) {
  function cmrToBez(t, pts) {
    var r = new Array();

    r.push(pts[1]);
    r.push(new Pt(pts[1].x - pts[0].x / 6 + pts[2].x / 6, pts[1].y - pts[0].y / 6 + pts[2].y / 6));
    r.push(new Pt(pts[2].x - pts[3].x / 6 + pts[1].x / 6, pts[2].y - pts[3].y / 6 + pts[1].y / 6));
    r.push(pts[2]);

    return r;
  }

  return compileBez(cmrToBez, pts);
}

function scalePoint(from, to) {
  var base = from;
  var r = to.sub(from);
  return function(pt) {
    var res = new Pt(base.x + r.x * pt.x - r.y * pt.y,
		     base.y + r.y * pt.x + r.x * pt.y);
    return res;
  };
}

var LINE = 'line';
var BSPLINE = 'bspline';
var CATMULL = 'catmull';

function Curve(cmp, pts) {
  this.compiler = cmp;
  this.pts      = pts;
};

Curve.prototype.reverse = function() {
  var nr = new Array();
  for (var i = this.pts.length-1; i >= 0; i--)
    nr.push(this.pts[i]);
  return new Curve(this.compiler, nr);
};

Curve.prototype.transform = function(f) {
  return new Curve(this.compiler, this.pts.map(function(p) { return f(p.x,p.y);}));
};

Curve.prototype.compile = function(from, to, typ) {
  var real = this.pts.map(scalePoint(from, to));
  if (typeof typ == 'undefined') {
    typ = this.compiler;
  }
  
  if (typ == LINE) {
    return compileLine(real);
  } else if (typ == BSPLINE) {
    return compileBspline(real);
  } else if (typ == CATMULL) {
    return compileCatmullRom(real);
  } else {
    alert('Bad t');
    return null;
  }
};


function BsplineCurve(pts) {
  return new Curve(BSPLINE, pts);
}
function CatmullRomCurve(pts) {
  return new Curve(CATMULL, pts);
}
function LineCurve(pts) {
  return new Curve(LINE, pts);
}


var api = new Object();
api.LineCurve = LineCurve;
api.CatmullRomCurve = CatmullRomCurve;
api.BsplineCurve = BsplineCurve;
api.Curve = Curve;
api.LINE = LINE;
api.BSPLINE = BSPLINE;
api.CATMULL = CATMULL;
return api;
}());