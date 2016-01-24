// ----------------------------------------------------------------------------------------
// Interactive document 
// ----------------------------------------------------------------------------------------
//
// * ".ia" elements are shown/hidden depending on their ia-key and ia-mode
// * ".ia-choice" are switching .ia elements based on ia-show and ia-hide
//         and their UI behaviour depends on their ia-ui-kind 
//
// ----------------------------------------------------------------------------------------

// Keeps the states of switches
var states = { };

// Is the specified ".ia-choice" selected? (meaning that all things it should show
// are shown and all things it should hide are hidden)
function isSelected(el) {
  var selected = true;
  el.data("ia-show").split(' ').forEach(function(k) { if (k != "") { selected = selected && states[k]; }});
  el.data("ia-hide").split(' ').forEach(function(k) { if (k != "") { selected = selected && !states[k]; }});
  return selected;
}

// Set a property of an element that has hover effect
// (data-ia-ui-prop can be used to change e.g. border color rather than background-color)
function setUiProp(el, v) {
  var prop = el.data("ia-ui-prop");
  el.css(prop == null ? "background-color" : prop, v);
}

// Highlight choice elements for all the currently expanded parts of the document
function updateChoices() {
  $(".ia-choice")
    .filter(function() {
      return $(this).data("ia-ui-kind") != null;
    })
    .each(function() {
      var el = $(this);
      if (isSelected(el)) {
        setUiProp($(this), $(this).data("ia-color").sel);
        setUiProp($(this).children(".ia-readmore"), $(this).data("ia-color").sel);
      } else {
        setUiProp($(this), $(this).data("ia-color").bg);      
        setUiProp($(this).children(".ia-readmore"), $(this).data("ia-color").bg);
      }
    });  
}

// For iterating over things in a loop
function RoundBuffer(items) {
  var index = 0;
  this.next = function() { 
    return items[(index++) % items.length];
  }
}

// Iterate over all the elements that can be used to expand/collapse things (.ia-choice)
// and register mouseover/mouseout events for them. Also add "read more" links to those
// marked with ".ia-ui-morelink" style
function initializeBoxes() {
  var colors = { };
  var selected = null;
  
  var palettes = 
    { box: new RoundBuffer([ 
        {bg:"#4F361D", sel:"#8C5E33"}, {bg:"#324C27", sel:"#547F42"}, 
        {bg:"#25444C",sel:"#3E727F"}, {bg:"#4C2D45",sel:"#7F4B74"} ]),
      light: new RoundBuffer([
        {sel:"#4F9589",bg:"#8DD3C7"}, {sel:"#827E9E",bg:"#BEBADA"},
        {sel:"#C27927",bg:"#FDB462"}, {sel:"#7AA530",bg:"#B3DE69"},
        {sel:"#B13628",bg:"#FB8072"}, {sel:"#37688A",bg:"#80B1D3"} ]) };


  $(".ia-choice")
    .filter(function() {
      return $(this).data("ia-ui-kind") != null;
    })
    .on("mouseenter", function() {      
      setUiProp($(this), $(this).data("ia-color").sel);
      setUiProp($(this).children(".ia-readmore"), $(this).data("ia-color").sel);
    })
    .on("mouseleave", function() {
      if (isSelected($(this))) return;
      setUiProp($(this), $(this).data("ia-color").bg);
      setUiProp($(this).children(".ia-readmore"), $(this).data("ia-color").bg);
    })
    .each(function() {
      var key = $(this).data("ia-key");
      var uikind = $(this).data("ia-ui-kind");
      if (colors[key] == null) colors[key] = palettes[uikind].next();
      $(this).data("ia-color", colors[key])
      setUiProp($(this), $(this).data("ia-color").bg);
    });    
    
  $(".ia-ui-morelink").each(function() {
    var align = $(this).hasClass("ia-ui-bar-left") ? "left" : "right;"
    $(this).append($("<p class='ia-readmore' data-ia-ui-prop='color' style='font-weight:bold; font-size:11pt; color:" + 
      $(this).data("ia-color").bg + "; text-align:" + align + "'><i style='margin-right:2px' class='fa fa-plus'></i> Read more</p>"));
  });        
}


// Hide or display the specified element (when toggling content display)
function toggleElement(el, visible) {
  if (visible) {
    var h = el.data("last-height");
    el.css("transform", "translate(0px, 0px) scaleY(1.0) scaleX(1.0)");  
    el.css("max-height", ((h==null||h<50) ? 1000 : h) + "px");
    el.css("opacity", "1.0");
  } else {
    el.data("last-height", el.height());
    el.css("transform", "translate(0px, -50%) scaleY(0.0) scaleX(0.5)");        
    el.css("max-height", "0px");
    el.css("opacity", "0.0");
  }    
}


// Update all elements that have the specified display key
function togglePart(key) {
  $(".ia").each(function() {
    if ($(this).data("ia-key") == key) {
      if ($(this).data("ia-mode") == "long") toggleElement($(this), states[key]);
      if ($(this).data("ia-mode") == "short") toggleElement($(this), !states[key]);
    }
  }); 
}

$(function() {  
  // Everything is collapsed by default
  $(".ia").each(function() { states[$(this).data("ia-key")] = false; });
  for(var key in states) togglePart(key);   
  
  // Register mouseover events and update elements to show current choices  
  initializeBoxes();  
  updateChoices();
  
  // Add toggle event handler for all the elements for choosing displayed content
  $(".ia-choice")
  .on("click", function(e) {
    var show = " " + $(this).data("ia-show") + " ";
    var hide = " " + $(this).data("ia-hide") + " ";
    var undoable = $(this).data("ia-undoable");
    var trueOrNot = (undoable && isSelected($(this))) ? false : true;
    for(var key in states) {
      if (show.indexOf(" " + key + " ") >= 0) states[key] = trueOrNot;
      if (hide.indexOf(" " + key + " ") >= 0) states[key] = !trueOrNot;
      togglePart(key);
    }    
    updateChoices();
    if (e.target == window.location + "#") e.preventDefault();
  });

  // This is needed for implementing the transitions correctly
  $(".ia").each(function() { 
    $(this).css("max-height", $(this).height());
  });  
  $(window).resize(function() {
    $(".ia").each(function() { 
      if (states[$(this).data("ia-key")])
        $(this).css("max-height", "1000px");
      else
        $(this).data("last-height", 1000);        
    });
  });
})

// ----------------------------------------------------------------------------------------
// Handling of slide-show elements
// ----------------------------------------------------------------------------------------

var slides = { };
$(function() {
  
  // Display one of the slides & enabled disable left/right arrows
  function displaySlide(id) {
    $("#" + id + " .slide").hide();
    $("#" + id + " .slide").eq(slides[id].current).show();
    
    var la = $("#" + id + " .larrow");
    if (slides[id].current == 0) la.addClass("larrow-disabled");
    else la.removeClass("larrow-disabled");
    
    var ra = $("#" + id + " .rarrow");
    if (slides[id].current == slides[id].count-1) ra.addClass("rarrow-disabled");
    else ra.removeClass("rarrow-disabled");
  }
  
  // For each ".ia-slide" element, count how many slides it has & add arrows
  $(".ia-slides").each(function() {
    var id = $(this).attr("id");
    slides[id] = {current:0, count:$("#" + id + " .slide").length };
    $(this).prepend($("<div class='larrow'></div>").on("click", function() {
        if ($(this).hasClass("larrow-disabled")) return;
        slides[id].current = (slides[id].current + slides[id].count - 1) % slides[id].count;
        displaySlide(id);
      })).prepend($("<div class='rarrow'></div>").on("click", function() {
        if ($(this).hasClass("rarrow-disabled")) return;
        slides[id].current = (slides[id].current + 1) % slides[id].count;
        displaySlide(id);        
      }));
    displaySlide(id);
  });  
});


// ----------------------------------------------------------------------------------------
// Simple celular automata that is shown in the "Stencil computations" section
// ----------------------------------------------------------------------------------------

$(function() {
  function get(input, i) { 
    var j = i < 0 ? i + input.length : (i >= input.length ? i - input.length : i);
    return input[j];
  }
  
  function stenc(input) {
    var output = new Array(input.length);
    for(var i = 0; i < input.length; i++) {
      var sum = get(input, i) + get(input, i-1) + get(input, i+1);
      output[i] = sum==2 || (sum==1&&get(input, i-1)==0) ? 1 : 0;            
    }
    return output;
  }
  
  var input = Array(250);
  for(var i=0; i<input.length; i++) input[i]=Math.random()<0.95?0:1;
  input[input.length-1] = 1;

  function addRow() {
    var strs = [];
    strs.push("<tr>");
    for(var j=0; j<input.length; j++) {
      strs.push("<td style='width:2px;height:2px;background:"+(input[j]==1?"black":"white")+"'></td>");
    }
    strs.push("</tr>");    
    input = stenc(input);
    $("#rule110").append($(strs.join("")));
    if ($("#rule110 tr").length >= 50) $("#rule110 tr").slice(0, 1).remove();
  }

  for(var j=0; j<50; j++) addRow();
  
  var intId = 0;
  $("#rule110btn").on("click", function() {
    if ($(this).html() == "Run") {
      intId = setInterval(addRow, 100);
      $(this).html("Stop");
    } else {
      clearInterval(intId);
      $(this).html("Run");      
    }
  })
})

// ----------------------------------------------------------------------------------------
// Playground for dataflow computations based on mouse X & Y position
// ----------------------------------------------------------------------------------------

// Keeps the specified number of past elements and adds new one to the front
// (moving the older ones further to the history)
function PastBuffer(count, initial) {
  var buffer = new Array(count);
  for(var i = 0; i < count; i++) buffer[i] = initial;
  this.get = function() { 
    return buffer; 
  }
  this.add = function(v) { 
    for(var i = count-1; i >= 0; i--) buffer[i] = buffer[i-1];
    buffer[0] = v;
  }          
}


// Updates the function in a playground
function setLiveChartFunction(prefix, xl, yl, fnc) {
  window[prefix + "-dfplayground"].setFunction(xl, yl, fnc);
}


// Create a dataflow playground - assumes that there is #<prefix>-drawinspace
function dataflowPlayground(prefix) {
  // Time series that are added to the charts
  var xseries = new TimeSeries();
  var yseries = new TimeSeries();
  var vseries = new TimeSeries();
  // This is the drawing space that user moves over
  var space = $("#" + prefix + "-drawingspace");

  // Is the chart currently running?
  var running = false;
  // Timer that stops the chart when nothing happens
  var timer = -1;
  
  // Created SmoothieCharts objects
  var chartIn = null;
  var chartOut = null;

  // Current function & buffer for values
  var f = null;
  var xs = null;
  var ys = null;

  // Save this instance in a global variable (for 'setLiveChartFunction')
  window[prefix + "-dfplayground"] = this;

  // Updates the function - called by 'setLiveChartFunction'
  this.setFunction = function(xl, yl, fnc) {
    xs = new PastBuffer(xl, 0);
    ys = new PastBuffer(yl, 0);
    f = fnc;  
  }


  // We keep last cursor position and add the points in 'updateSeries' once every 50ms
  var running = -1;
  var cursorX;
  var cursorY;

  var moveOrTouchHandler = function(event) { 
    if (running == -1) { 
      running = setInterval(updateSeries, 50); chartIn.start(); chartOut.start(); 
    }
    if (timer != -1) clearTimeout(timer);
    timer = setTimeout(function() { chartIn.stop(); chartOut.stop(); clearInterval(running); running = -1; }, 2000);
    
    event.preventDefault();
    var px = event.pageX || event.originalEvent.targetTouches[0].pageX;
    var py = event.pageY || event.originalEvent.targetTouches[0].pageY;
    cursorX = (px - $(this).offset().left) / space.width() * 100;
    cursorY = (py - $(this).offset().top) / space.height() * 100;
  }

  function updateSeries() {
    var t = new Date().getTime();
    xseries.append(t, cursorX);
    yseries.append(t, cursorY);
    if (f != null) {
      xs.add(cursorX);
      ys.add(cursorY);
      vseries.append(t, f(xs.get())(ys.get()));
    }
  };

  space.on("touchmove", moveOrTouchHandler);
  space.on("mousemove", moveOrTouchHandler);

  // Create the chart controls
  
  $("#chartIn").attr("width", $("#" + prefix + "-input").outerWidth()-4);
  $("#chartOut").attr("width", $("#" + prefix + "-input").outerWidth()-4);
  chartIn = new SmoothieChart({ grid:{strokeStyle:'rgba(119,119,119,0.44)',verticalSections:5,borderVisible:false}, labels:{disabled:true}, interpolation:'linear', millisPerPixel:10,enableDpiScaling:false });
  chartIn.addTimeSeries(xseries, { strokeStyle: 'rgba(64, 96, 64, 1)', fillStyle: 'rgba(0, 0, 0, 0)', lineWidth: 4 });
  chartIn.addTimeSeries(yseries, { strokeStyle: 'rgba(64, 64, 96, 1)', fillStyle: 'rgba(0, 0, 0, 0)', lineWidth: 4 });
  chartIn.streamTo(document.getElementById("chartIn"), 0);
  chartIn.stop();
  
  chartOut = new SmoothieChart({ grid:{strokeStyle:'rgba(119,119,119,0.44)',verticalSections:5,borderVisible:false}, labels:{disabled:true}, interpolation:'linear', millisPerPixel:10,enableDpiScaling:false });
  chartOut.addTimeSeries(vseries, { strokeStyle: 'rgba(255, 128, 128, 1)', fillStyle: 'rgba(0, 0, 0, 0)', lineWidth: 4 });
  chartOut.streamTo(document.getElementById("chartOut"), 0);
  chartOut.stop();
}