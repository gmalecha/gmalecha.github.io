function resizeImage(img) {
    var sx = (500 - 100) / img.width;
    var sy = (500 - 100) / img.height;

    var k = Math.max(sx, sy);

    img.width *= sx;
    img.height *= sy;
}

function setPieceCount(pc) {
    document.getElementById('PieceCount').innerHTML = pc;
}

function setPuzzle(imgPath, xp, yp, svgDoc) {
    var img = new Image();
    img.onload = function() {
        resizeImage(img);
	puzzle = new puz.Puzzle(svgDoc, img,
                                document.getElementById('Puzzle'));
	makePuzzle(puzzle, yp, xp, setPieceCount);
        setPieceCount(puzzle.remainingPieces());
        document.getElementById('Preview').src = imgPath;
	scramblePuzzle(puzzle);

        document.getElementById('Board').puzzle = puzzle;

        window.setTimeout(1, svgDoc.forceRedraw());
    };
    img.src = imgPath;
}

function clear() {
    var p = document.getElementById('Puzzle');
    while (p.childNodes.length > 0) {
        p.removeChild(p.childNodes.item(0));
    }
}

function create() {
    var cols = parseInt(document.getElementById('cols').value);
    var rows = parseInt(document.getElementById('rows').value);
    var img_url = document.getElementById('img_url').value;

    clear();

    setPuzzle(img_url, cols, rows, document.getElementById('BoardSVG'));
}

$(function(){create();});
