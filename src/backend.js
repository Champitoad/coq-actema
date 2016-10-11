function backend_new_node (element, callback) {
    var hammertime = new Hammer (element);
    hammertime.get ('pan').set ({ direction: Hammer.DIRECTION_ALL });
    hammertime.get ('swipe').set ({ direction: Hammer.DIRECTION_ALL });
    hammertime.on('pan tap press pinch rotate doubletap panstart panend panmove', function(ev) {
	callback (ev);
    });
}

function backend_notify (msg) {
    $.notify (msg);
}
