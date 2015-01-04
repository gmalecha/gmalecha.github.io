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
function divideLength(str, i) {
  return (parseInt(str) / i) + str.substring(str.length-2);
}

function addLength(str1, str2) {
   return (parseInt(str1) + parseInt(str2)) + str1.substring(str1.length-2);
}

function pad(x) {
  if( x < 10 ) return "0" + x;
  return "" + x;
}

function generateClickHandler(puzzle) {
    return function(e) {
	var id = e.target.parentNode.id;
	var x = parseInt(id.substring(id.lastIndexOf('_')+1));
	puzzle.slideTile(x);
    };
}

function constructSlidingTilePuzzle(puzzle, div, id, img_url,
				    offsetx, offsety, tx, ty, tw, th, matrix) {
  while( div.childNodes.length != 0 ) {
    div.removeChild(div.childNodes[0]);
  }
  for(var i = 0; i < tx * ty; i++) {
    if( matrix[i] == -1 ) continue;

    var x = i % tx;
    var y = Math.floor(i / tx);
    var di = document.createElement('div');
    di.id = id + i;
    di.style.width = addLength(tw, -1);
    di.style.height = addLength(th, -1);
    di.className = 'puzzle_piece';

    di.style.top  = addLength((-(y+x + y*(tx-1)) * (parseInt(th)-1)) + "pt",
			      divideLength(th, 1. / y));
    di.style.left = addLength("0pt", divideLength(tw, 1. / x));



    var img = document.createElement('img');
    img.src = img_url;
    img.style.width = div.style.width;
    img.style.height = div.style.height;
    img.style.left = divideLength(tw, -1. / x);
    img.style.top = divideLength(th, -1. / y);

    di.appendChild(img);

    img.onclick = generateClickHandler(puzzle);
    div.appendChild(di);
  }
}

function Puzzle(win, div, imageUrl, tx, ty) {
  this.tilesX = tx;
  this.tilesY = ty;
  this.tileWidth = divideLength(div.style.width, this.tilesX);
  this.tileHeight = divideLength(div.style.height, this.tilesY);
  this.idPrefix = "Puzzle_" + div.id + "_" + Math.random() + "_";
  this.initialEmpty = tx*ty-1;
  this.moveDelay = 50;
  this.window = win;
  var self = this;

  this.mat = new Array();
  var count = 0;
  for( i = 0; i < this.tilesX * this.tilesY; i++ ) {
      if( i == this.initialEmpty )
        this.mat[i] = -1;
      else
        this.mat[i] = count++;
  }

  constructSlidingTilePuzzle(this, div, this.idPrefix, imageUrl,
			     div.offsetLeft+"pt", div.offsetTop + "pt",
			     this.tilesX, this.tilesY,
			     this.tileWidth, this.tileHeight, this.mat);

  function slide(id, dx, dy, delay, callback) {
    var d = document.getElementById(id);
    var startX = d.style.left;
    var startY = d.style.top;
    if( delay == 0 ) {
      if( 0 != dy )
        d.style.top = addLength(startY, divideLength(this.tileHeight, dy));
      if( 0 != dx )
        d.style.left = addLength(startX, divideLength(this.tileWidth, dx));
      callback.call(self);
    } else {
	for( i = 0; i < 4; i++ ) {
	  this.window.setTimeout(function() {
	    //var d = document.getElementById(id);
	    if( 0 != dy )
	      d.style.top = addLength(d.style.top,
				      divideLength(self.tileHeight, dy * 5));
	    if( 0 != dx )
	      d.style.left = addLength(d.style.left,
				       divideLength(self.tileWidth, dx * 5));
	  }, i * delay / 5);
	}
      this.window.setTimeout(function(e) {
        //var d = document.getElementById(id);
        if( 0 != dy )
          d.style.top = addLength(startY, divideLength(self.tileHeight, dy));
        if( 0 != dx )
          d.style.left = addLength(startX, divideLength(self.tileWidth, dx));

	callback.call(self);
      }, delay);
    }
  }

  function getTilePosition(ary, x) {
    for(i = 0; i < this.tilesX * this.tilesY; i++) {
      if( ary[i] == x ) return i;
    }
    return -1;
  }

  function slideTile(tile) {
    var pos = this.getTilePosition(this.mat, tile);
    if( pos == -1 ) return;
    x = pos % this.tilesX;
    y = Math.floor(pos / this.tilesX);

    nx = x; ny = y;

    if( x > 0 && this.mat[y * this.tilesX + x - 1] == -1 )  {
      // Slide Left
      nx--;
    } else if( x < this.tilesX-1 && this.mat[y * this.tilesX + x + 1] == -1 ) {
      // Slide Right
      nx++;
    } else if( y > 0 && this.mat[(y-1) * this.tilesX + x] == -1 ) {
      // Slide Up
      ny--;
    } else if( y < this.tilesY-1 && this.mat[(y+1) * this.tilesX + x] == -1 ) {
      // Slide Down
      ny++;
    } else {
      // Can't slide
      return;
    }
    this.slide(this.idPrefix + tile, nx-x, ny-y, this.moveDelay,
	       function() {
		   this.mat[pos] = -1;
		   this.mat[ny * self.tilesX + nx] = tile;
	       });
  }

  function slideDirection(dir) {
    pos = this.getTilePosition(this.mat, -1);
    if( pos == -1 ) return;
    x = pos % this.tilesX;
    y = Math.floor(pos / this.tilesX);
    //alert(x + "  " + y);
    switch( dir ) {
      case 0:
        x--;
        break;
      case 1:
        x++;
        break;
      case 2:
        y--;
        break;
      case 3:
        y++;
        break;
    }
    if( y < 0 || y >= this.tilesY || x < 0 || x >= this.tilesX ) return;
    this.slideTile(this.mat[y * this.tilesX + x]);
  }

  this.slide = slide;
  this.slideTile = slideTile;
  this.slideDirection = slideDirection;
  this.getTilePosition = getTilePosition;

  return this;
}

function randomizePuzzle(puzzle) {
  var time = puzzle.moveDelay;
  puzzle.moveDelay = 0;
  for(var i = 0; i < 500; i++) {
    var t = Math.floor(2*Math.random())+1;
    var d = Math.floor(4*Math.random());
    //alert(d + " x " + t);
    while( t-- > 0 ) {
      puzzle.slideDirection(d);
    }
  }
  puzzle.moveDelay = time;
}
