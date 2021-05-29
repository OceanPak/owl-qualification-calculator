var ideal_hour = 0
var ideal_minute = 30

var loop = setInterval(function() {
    var d = new Date();
    if (d.getHours() == ideal_hour && d.getMinutes() == ideal_minute) {
        location.reload();
    }
  }, 1000);