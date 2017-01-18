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
var puz = (function() {
var SVG_NS = 'http://www.w3.org/2000/svg';
var XLINK_NS = 'http://www.w3.org/1999/xlink';
var HTML_NS = 'http://www.w3.org/HTML/Strict/1.0';

function PuzzlePiece(puz, vis, clip, nodes) {
  this.container = vis;
  this.mask      = clip;
  this.nodes     = nodes;
  this.puzzle    = puz;

  this.xlate     = new Pt(0,0);
  this.handle    = this.puzzle.nodePoint(nodes[0][0]);
  this.rotate    = 0;
}

function updateXform(pp) {
  var bb = pp.container.getBBox();

  var cx = bb.width / 2;
  var cy = bb.height / 2;

  var fx = pp.puzzle.doc.createSVGTransformList();

  var xform = pp.puzzle.doc.createSVGTransform();
  xform.setTranslate(-cx, -dy);
  fx.appendItem(xform);

  xform = pp.puzzle.doc.createSVGTransform();
  xform.setRotate(pp.rotate);
  fx.appendItem(xform);

  xform = pp.puzzle.doc.createSVGTransform();
  xform.setTranslate(cx + pp.xlate.x, cy + pp.xlate.y);
  fx.appendItem(xform);

  fx.consolidate();

  pp.container.transform.baseVal = fx;
};

PuzzlePiece.prototype.move = function(dx, dy) {
  this.xlate = this.xlate.add(new Pt(dx, dy));
  var xform = this.puzzle.doc.createSVGTransform();
  xform.setTranslate(dx, dy);
  this.container.transform.baseVal.appendItem(xform);
  this.container.transform.baseVal.consolidate();
};

PuzzlePiece.prototype.moveTo = function(x,y) {
  var d = new Pt(x,y).sub(this.xlate.add(this.handle));
  return this.move(d.x, d.y);
};

PuzzlePiece.prototype.rotate = function(angle) {
  this.rotate += angle;
  updateXform(this);
};

PuzzlePiece.prototype.anchorHandle = function(anchor) {
  if (this.anchors.indexOf(anchor) != -1) {
    var a = this.puzzle.anchorPoints(anchor);
    var d = new Pt(this.container.clientLeft, this.container.clientTop);
    return a.map(d.add);
  } else {
    return null;
  }
};

PuzzlePiece.prototype.allAnchors = function() {
  var res = [];
  for (i in allAnchors) {
    res.push(i);
  }
  return res;
};

function Puzzle(svgDoc, image, container) {
  this.hash   = Math.round(Math.random() * 1000000000);
  this.doc    = svgDoc;
  this.image  = image;
  this.size   = new Pt(image.width, image.height);
  this.owners = {};

  // Set up the SVG Document
  this.surface = container;

  // Puzzles are graphs
  this.nodes = new Array();
  this.edges = {};
  this.pieces = {};
  this.pieceCount = 0;
}

function svgLoop(nodes, edges, path) {
  var from = nodes[path[0]];
  var acc = "M" + from.x + "," + from.y;
  for (var idx = 0; idx < path.length; idx++) {
    var next = (idx + 1) % path.length;
    if (edges[path[idx]+','+path[next]] == undefined) {
      alert('Anomoly Please Report: ' + path[idx] + '  ' + path[next]);
    }
    acc += " " + edges[path[idx]+','+path[next]].compile(nodes[path[idx]],
							 nodes[path[next]]);
    from = nodes[path[idx]];
  }
  return acc + ' Z';
}

Puzzle.SNAP_DISTANCE = 5;

Puzzle.prototype.dimensions = function() {
  return new Pt(this.image.width, this.image.height);
};

Puzzle.prototype.nodePoint = function(n) {
  return this.nodes[n];
};

Puzzle.prototype.cmpAnchor = function(l, r) {
  var ml = this.nodes[l];
  var mr = this.nodes[r];

  if (ml.y == mr.y) {
    return ml.x - mr.x;
  } else {
    return ml.y - mr.y;
  }
};

Puzzle.prototype.createNode = function(x, y) {
    var nn = this.nodes.length;
    this.nodes.push(new Pt(x,y));
    return nn;
};
Puzzle.prototype.createEdge = function(n1, n2, pts) {
    if (n1 == n2) return false;
    this.edges[n1+','+n2] = pts;
    this.edges[n2+','+n1] = pts.transform(function(x,y) { return new Pt(x,-1*y);});
    return true;
};

Puzzle.prototype.remainingPieces = function() {
  var c = 0;
  for (var i in this.pieces) {
    c++;
  }
  return c;
};

function setupPiece(puz, pid, anchors, clipper) {
  // Clear the clipper
  while (clipper.childNodes.length > 0) {
    clipper.removeChild(clipper.childNodes.item(0));
  }

  // Set up the clipper
  var first = true;
  var fp = "";

  for (var e in anchors) {
    var edge = anchors[e];

    if (first) {
      fp += ' ' + svgLoop(puz.nodes, puz.edges, edge);
    } else {
      fp += ' ' + svgLoop(puz.nodes, puz.edges, edge.slice(0).reverse());
    }
    first = false;
  }
  var path = puz.doc.ownerDocument.createElementNS(SVG_NS, 'path');
  path.setAttribute('d', fp);
  clipper.appendChild(path);

  // Set up the owners
  for (e in anchors) {
    var edge = anchors[e];
    for (var i = 0; i < edge.length; i++) {
      var id = edge[i]+','+edge[(i+1)%edge.length];
      if (!puz.owners.hasOwnProperty(id))
	puz.owners[id] = new Array();
      puz.owners[id].push(pid);
    }
  }
}


Puzzle.prototype.createPiece = function(anchors) {
  var piece_id = this.pieceCount++;
  // TODO : Refactor to call setupPiece

  var ns = this.nodes;

  // Create the clip-path
  var clp = this.doc.ownerDocument.createElementNS(SVG_NS, 'clipPath');
  clp.setAttribute('id', this.hash + '_' + piece_id);
  clp.setAttribute('clipPathUnits', 'userSpaceOnUse');

  setupPiece(this, piece_id, anchors, clp);

  // Create the visual element
  var vis = this.doc.ownerDocument.createElementNS(SVG_NS, 'g');
  vis.setAttribute('clip-path', "url(#" + this.hash + "_" + piece_id + ")");
  vis.setAttributeNS(SVG_NS, 'clip-rule', 'evenodd');
  var img = this.doc.ownerDocument.createElementNS(SVG_NS, 'image');
  img.setAttributeNS(XLINK_NS, 'href', this.image.src);
  img.setAttribute('x',     '0');
  img.setAttribute('y',     '0');
  img.setAttribute('width',   this.image.width);
  img.setAttribute('height',  this.image.height);
  vis.appendChild(img);

  // Add the nodes to the document
  this.surface.appendChild(vis);
  this.surface.insertBefore(clp, vis);

  var p = new PuzzlePiece(this, vis, clp, anchors);
  this.pieces[piece_id] = p;

  p.id = piece_id;

  return p;
};

Puzzle.prototype.lookupOwners = function(from, to) {
  return this.owners[from + ',' + to];
};

Puzzle.prototype.removePiece = function(p) {
  if (p.puzzle != this)  return false;
  delete this.pieces[p.id];
  for (o in this.owners) {
    this.owners[o] = this.owners[o].filter(function (x) { return x != p; });
  }
  this.surface.removeChild(p.container);
  this.surface.removeChild(p.mask);
  p.container = null;
  p.mask = null;
  delete this.pieces[p.id];
  return true;
};

Puzzle.prototype.tryJoin = function(p) {
  var edges = new Array()
  for (var ei in p.nodes) {
    var edge = p.nodes[ei];
    for (var i = 0; i < edge.length; i++) {
      edges.push(edge[(i+1)%edge.length]+','+edge[i]);
    }
  }

  for (var i in edges) {
    var owners = this.owners[edges[i]];
    for (var j in owners) {
      if (owners[j] == p.id) continue;
      var q = this.pieces[owners[j]];
      if (q == undefined) continue;
      if (q.xlate.sub(p.xlate).magnitude() <= Puzzle.SNAP_DISTANCE &&
	  q.rotate == p.rotate) {
	return q;
      }
    }
  }
  return null;
};

function edgesForNodes(ls, fnc) {
  for (var i = 0; i < ls.length; i++) {
    fnc(ls[i], ls[(i+1)%ls.length]);
  }
}

Puzzle.prototype.join = function(l, r) {
  var me = this;

  function sortEdge(edge) {
    var minI = 0;
    for (var i = 1; i < edge.length; i++) {
      if (me.cmpAnchor(edge[minI], edge[i]) > 0) {
	minI = i;
      }
    }
    // Might need to reverse
    var base = me.nodes[edge[minI]];
    if (cross(me.nodes[edge[(minI+1)%edge.length]].sub(base),
	      me.nodes[edge[(minI+edge.length-1)%edge.length]].sub(base)) < 0) {
      edge = edge.reverse();
      edge = edge.slice(edge.length - minI).concat(edge.slice(0, edge.length-minI));
    } else {
      edge = edge.slice(minI).concat(edge.slice(0, minI));
    }
    return edge;
  }
  function nextAnchor(edges, d, i) {
    for (var ei in edges) {
      var e = edges[ei];
      if (e.indexOf(i) != -1) {
	return e[(e.indexOf(i)+d+e.length)%e.length];
      }
    }
    return -1;
  }
  function hasEdge(nds, f, t, d) {
    for (var i = 0; i < nds.length; i++) {
      if ((nds[i] == f && nds[(i+d+nds.length)%nds.length] == t))
	return i;
    }
    return -1;
  }

  function gatherEdge(left, right, e, at, d, acc) {
    function nextInRight(f,t) {
      for (var i in right) {
	if (hasEdge(right[i], f, t, -1) != -1) return i;
      }
      return -1;
    }

    var cur = left[e][at];
    var next = left[e][(at+1)%left[e].length];

    if (hasEdge(acc, cur, next, 1) != -1) return sortEdge(acc);

    var nr = nextInRight(cur, next);
    if (nr == -1) {
      acc.push(cur);
      return gatherEdge(left, right, e, (at+1) % left[e].length, d, acc);
    } else {
      var k = hasEdge(right[nr], cur, next, -1);
      return gatherEdge(right, left, nr, k, -d, acc);
    }
  }

  // Gather all of the edges
  var seen_edges = new Array();
  l.nodes.forEach(function(edge) {
		    edgesForNodes(edge, function(a,b) {
				    if (nextAnchor(r.nodes, -1, a) == b ||
					nextAnchor(r.nodes, 1, a) == b)
				      seen_edges[b+','+a] = seen_edges[a+','+b] = true;
				  });
		  });
  var new_perimeter = new Array();

  for (var e = 0; e < l.nodes.length; e++) {
    var edge = l.nodes[e];
    for (var i = 0; i < edge.length - 1; i++) {
      if (seen_edges.hasOwnProperty(edge[i] + ',' + edge[i+1])) continue;

      var ne = gatherEdge(l.nodes, r.nodes, e, i, 1, new Array());
      edgesForNodes(ne, function(a,b) { seen_edges[b+','+a] = seen_edges[a+','+b] = true; });

      new_perimeter.push(ne);
    }
  }

  for (e = 0; e < r.nodes.length; e++) {
    var edge = r.nodes[e];
    for (var i = 0; i < edge.length - 1; i++) {
      if (seen_edges.hasOwnProperty(edge[i] + ',' + edge[i+1])) continue;

      var ne = gatherEdge(r.nodes, l.nodes, e, i, 1, new Array());
      edgesForNodes(ne, function(a,b) { seen_edges[b+','+a] = seen_edges[a+','+b] = true; });

      new_perimeter.push(ne);
    }
  }

  // Sort the edges by their first anchor to determine the "perimeter"
  new_perimeter.sort(function(l,r) {
		       return me.cmpAnchor(r[0], l[0]) < 0; // TODO
		     });

  // Update the owners
  this.removePiece(r);
  setupPiece(this, l.id, new_perimeter, l.mask);
  l.nodes = new_perimeter;

  return l;
};

var api = new Object();
api.Puzzle = Puzzle;
return api;
})();
