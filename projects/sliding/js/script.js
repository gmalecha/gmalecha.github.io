var puz;
function update(div, url, tx, ty, w, h) {
  div.style.width = w;
  div.style.height = h;

  puz = new Puzzle(window, div, url, tx, ty);
}

function updateFromDocument() {
  var url = document.getElementById('image_url').value;
  var tiles_x = document.getElementById('tile_x').value;
  var tiles_y = document.getElementById('tile_y').value;
  var width = document.getElementById('puzzle_width').value;
  var height = document.getElementById('puzzle_height').value;

  var puzzle_frame = document.getElementById('puzzle_frame');
  var puzzle_div = document.getElementById('puzzle_div');

  var iwidth = parseInt(width);
  var iheight = parseInt(height);

  width = addLength(width, tiles_x * Math.floor(iwidth / tiles_x) - iwidth);
  height = addLength(height, tiles_y * Math.floor(iheight / tiles_y) - iheight);

  puzzle_frame.style.width = width;
  puzzle_frame.style.height = height;

  update(puzzle_div, url, tiles_x, tiles_y, width, height);
}

$(updateFromDocument);
