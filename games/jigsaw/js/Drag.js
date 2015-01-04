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
function drag(elem, start, move, stop) {
    var me = new Object();
    var doc = elem.ownerDocument;
    elem.onmousedown = function(e) {
	me.loc = {'x' : e.clientX, 'y' : e.clientY};
	me.elem = elem;
	if (start(e, me.elem, me.loc['x'], me.loc['y'])) {
	    doc.onmousemove = function(e) {
		move(e, elem, 
		     e.clientX - me.loc['x'],
		     e.clientY - me.loc['y']);
		me.loc = {'x' : e.clientX, 'y' : e.clientY};
	    };
	    doc.onmouseup = function(e) {
		doc.onmousemove = null;
		doc.onmouseup = null;
		stop(e, me.elem, e.clientX, e.clientY);
	    };
	}
    };
}

function undrag(elem) {
  elem.onmousedown = function(){};
}