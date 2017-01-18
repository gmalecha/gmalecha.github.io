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
function perpOut(p1, p2) {
  var x = p2.x - p1.x;
  var y = p2.y - p1.y;
  var d = Math.sqrt(x * x + y * y);
  return new Pt(y / d, -x / d);
}

// Returns the angle
function cross(v1, v2) {
  return v1.x * v2.y - v1.y * v2.x;
}

function Pt(x, y) {
    this.x = x;
    this.y = y;
}

Pt.prototype.toString = function() {
    return this.x + "," + this.y;
};
Pt.prototype.add = function(p) {
    return new Pt(this.x + p.x, this.y + p.y);
};
Pt.prototype.sub = function(p) {
    return new Pt(this.x - p.x, this.y - p.y);
};
Pt.prototype.mult = function(d) {
    return new Pt(this.x * d, this.y * d);
};
Pt.prototype.magnitude = function() {
    return Math.sqrt(this.x*this.x + this.y*this.y);   
};
Pt.prototype.distance = function(p) {
    return this.sub(p).magnitude();
};

Pt.prototype.toString = function(){
  return '(' + this.x + ',' + this.y + ')';
};


