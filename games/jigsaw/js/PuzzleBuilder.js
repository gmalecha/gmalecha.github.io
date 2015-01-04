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
function makePuzzle(puz, rows, cols, updateCount) {
  var nodes = new Array();
  var dims = puz.dimensions();
  var width = dims.x;
  var height = dims.y;
  
  // Make corners
  for (var r = 0; r <= rows; r++) {
    for (var c = 0; c <= cols; c++) {
      var x = (c + ((c == 0 || c == cols) ? 0 : (0.25 * Math.random() - 0.125))) * (width / cols);
      var y = (r + ((r == 0 || r == rows) ? 0 : (0.25 * Math.random() - 0.125))) * (height / rows);
      nodes.push(puz.createNode(x, y));
    }
  }
  
  // The edges
  var edgeCurve = curves.LineCurve([new Pt(0.,0.),new Pt(1.,0.)]);
  for (r = 0; r < rows; r++) {
    puz.createEdge(nodes[r * (cols + 1)],
		   nodes[(r+1) * (cols + 1)],
		   edgeCurve);
    puz.createEdge(nodes[r * (cols + 1) + cols], 
		   nodes[(r+1) * (cols + 1) + cols],
		   edgeCurve);
  }
  for (c = 0; c < cols; c++) {
    puz.createEdge(nodes[c],
		   nodes[c+1],
		   edgeCurve);
    puz.createEdge(nodes[c + rows*(cols+1)], 
		   nodes[c + rows*(cols+1) + 1],
		   edgeCurve);
  }

  function randomEdge() {
    var x1 = 0.0;
    var y1 = 0.0;
    var x2 = 1.0;
    var y2 = 0.0;

    var mx = (x1 + x2) / 2;
    var my = (y1 + y2) / 2;

    var p = perpOut(new Pt(x1, y1), new Pt(x2, y2));

    if (Math.random() < 0.5) {
      p.x *= -1;
      p.y *= -1;
    }

    var d = Math.sqrt((x2-x1)*(x2-x1) + (y2-y1)*(y2-y1));
    
    var px = mx + p.x * d * 0.2;
    var py = my + p.y * d * 0.2;
    
    var mxl = x1 + (x2 - x1) * 0.45;
    var myl = y1 + (y2 - y1) * 0.45;

    var mxl2 = x1 + (px - x1) * 3.5 / 5;
    var myl2 = y1 + (py - y1) * 3.5 / 5;
    var mxl1 = mxl + (mxl2 - mxl) / 2;
    var myl1 = myl + (myl2 - myl) / 2;

    var mxu = x1 + (x2 - x1) * 0.55;
    var myu = y1 + (y2 - y1) * 0.55;

    var mxu2 = x2 + (px - x2) * 3.5 / 5;
    var myu2 = y2 + (py - y2) * 3.5 / 5;
    var mxu1 = mxu + (mxu2 - mxu) / 2;
    var myu1 = myu + (myu2 - myu) / 2;

    var pts = new Array();
    pts.push(new Pt(x1, y1));

    pts.push(new Pt(mxl, myl));   
    pts.push(new Pt(mxl1, myl1));
    pts.push(new Pt(mxl2, myl2));
    
    pts.push(new Pt(px, py));

    pts.push(new Pt(mxu2, myu2));
    pts.push(new Pt(mxu1, myu1));
    pts.push(new Pt(mxu, myu));

    pts.push(new Pt(x2, y2));

    return curves.BsplineCurve(pts);
  }

  for (c = 1; c < cols; c++) {
    puz.createEdge(nodes[c], nodes[c+cols+1], randomEdge());
  }
  for (r = 1; r < rows; r++) {
    puz.createEdge(nodes[r*(cols+1)], nodes[r*(cols+1)+1], randomEdge());
  }

  for (r = 1; r < rows; r++) {
    for (c = 1; c < cols; c++) {
      puz.createEdge(nodes[r*(cols+1)+c], nodes[r*(cols+1)+c+1], randomEdge());
      puz.createEdge(nodes[r*(cols+1)+c], nodes[(1+r)*(cols+1)+c], randomEdge());
    }
  }

  // The pieces
  for (r = 0; r < rows; r++) {
    for (c = 0; c < cols; c++) {
      var base = r*(cols+1)+c;
      var p = puz.createPiece([[base, base+1, base+cols+2, base+cols+1]]);
      (function(p, updateCount) {
	 drag(p.container, 
	      function(e,o,x,y){ 
		return true;
	      },
	      function(e,o,dx,dy){p.move(dx,dy);},
	      function(e,o,x,y){
		var jc = puz.tryJoin(p);
		while (jc != null) {
		  puz.join(p, jc); 
		  jc = puz.tryJoin(p);
		}
		if (updateCount != undefined) {
		  updateCount(puz.remainingPieces());
		}
		if (puz.remainingPieces() == 1) {
		  alert('You win!');
		  var nc = p.xlate.mult(-1);
		  p.move(nc.x, nc.y);
		  undrag(p.container);
		}
	      });
       })(p, updateCount);
    }
  }
}

function scramblePuzzle(puz) {
  var dims = puzzle.dimensions();
  for (var id in puz.pieces) {
    puz.pieces[id].moveTo(Math.random()*dims.x, Math.random()*dims.y);
  }
}
