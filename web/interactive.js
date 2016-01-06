// Interactive document 
// --------------------
//
// * ".ia" elements are shown/hidden depending on their ia-key and ia-mode
// * ".ia-choice" are switching .ia elements based on ia-show and ia-hide
//         and their UI behaviour depends on their ia-ui-kind 
//

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


function setUiProp(el, v) {
  var prop = el.data("ia-ui-prop");
  el.css(prop == null ? "background-color" : prop, v);
}

// 
function updateChoices() {
  $(".ia-choice").each(function() {
    var el = $(this);
    if (isSelected(el)) setUiProp($(this), $(this).data("ia-color").sel);
    else setUiProp($(this), $(this).data("ia-color").bg);      
  });  
}

// For iterating over things in a loop
function RoundBuffer(items) {
  var index = 0;
  this.next = function() { 
    return items[(index++) % items.length];
  }
}

//
function initializeBoxes() {
  var colors = { };
  var selected = null;
  
  var palettes = 
    { box: new RoundBuffer([ 
        {bg:"#4F361D", sel:"#8C5E33"}, {bg:"#324C27", sel:"#547F42"}, 
        {bg:"#25444C",sel:"#3E727F"}, {bg:"#4C2D45",sel:"#7F4B74"} ]),
      circle: new RoundBuffer([
        {sel:"#4F9589",bg:"#8DD3C7"}, {sel:"#827E9E",bg:"#BEBADA"},
        {sel:"#B13628",bg:"#FB8072"}, {sel:"#37688A",bg:"#80B1D3"},
        {sel:"#C27927",bg:"#FDB462"}, {sel:"#7AA530",bg:"#B3DE69"} ]) };
  
  $(".ia-choice")
    .on("mouseenter", function() {      
      setUiProp($(this), $(this).data("ia-color").sel);
    })
    .on("mouseleave", function() {
      if (isSelected($(this))) return;
      setUiProp($(this), $(this).data("ia-color").bg);
    })
    .each(function() {
      var key = $(this).data("ia-key");
      if (colors[key] == null)
        colors[key] = palettes[$(this).data("ia-ui-kind")].next();
      $(this).data("ia-color", colors[key])
      setUiProp($(this), $(this).data("ia-color").bg);
    });
}

//
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

//
function togglePart(key) {
  $(".ia").each(function() {
    if ($(this).data("ia-key") == key) {
      if ($(this).data("ia-mode") == "long") toggleElement($(this), states[key]);
      if ($(this).data("ia-mode") == "short") toggleElement($(this), !states[key]);
    }
  }); 
}

$(function() {

  $(".ia").each(function() { states[$(this).data("ia-key")] = false; });
  for(var key in states) togglePart(key);   
    
  initializeBoxes();  
  updateChoices();
  
  $(".ia-choice")
  .on("click", function(e) {
    var show = " " + $(this).data("ia-show") + " ";
    var hide = " " + $(this).data("ia-hide") + " ";
    var trueOrNot = isSelected($(this)) ? false : true;
    for(var key in states) {
      if (show.indexOf(" " + key + " ") >= 0) states[key] = trueOrNot;
      if (hide.indexOf(" " + key + " ") >= 0) states[key] = !trueOrNot;
      togglePart(key);
    }    
    updateChoices();
    if (e.target == window.location + "#") e.preventDefault();
  });
  

/*  
  $(".ia")
    .on("click", function() {
      var key = $(this).data("ia-key");
      states[key] = !states[key];
      togglePart(key);            
    })
    .each(function() {
      var key = $(this).data("ia-key");
      if (states[key] == null)
      {
        //$("<div class='ia-expand'><i class='fa fa-cubes'></i></div>").insertBefore($(this));
      }
      states[key] = true;
    });
*/

/*
  for(var key in states)
  {
      states[key] = false;
      togglePart(key);
  }
*/  
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


var slides = { };
$(function() {
  function displaySlide(id)
  {
    $("#" + id + " .slide").hide();
    $("#" + id + " .slide").eq(slides[id].current).show();
    var la = $("#" + id + " .larrow");
    if (slides[id].current == 0) la.addClass("larrow-disabled");
    else la.removeClass("larrow-disabled");
    var ra = $("#" + id + " .rarrow");
    if (slides[id].current == slides[id].count-1) ra.addClass("rarrow-disabled");
    else ra.removeClass("rarrow-disabled");
  }
  
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

/*

var lightPalette = [ {bg:"transparent", sel:"#b3e2cd"}, {bg:"transparent", sel:"#fdcdac"}, 
  {bg:"transparent", sel:"#cbd5e8"}, {bg:"transparent", sel:"#f4cae4"}, 
  {bg:"transparent", sel:"#e6f5c9"}, {bg:"transparent", sel:"#fff2ae"}, 
  {bg:"transparent", sel:"#f1e2cc"} ];
*/

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