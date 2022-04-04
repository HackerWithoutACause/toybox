
Prism.languages['toybox'] = {
    'keyword': /(^|\W)(def|while|do|end|if|then|for|let|else)(\W|$)/i,
    'literal': /[0-9]+|true|false/,
    'string': {
        greedy: true,
        pattern: /(?:"(?:\\(?:\r\n|[\s\S])|[^"\\\r\n])*"|'(?:\\(?:\r\n|[\s\S])|[^'\\\r\n])*')/g
    }
}

      let output = document.getElementById("outputs");

      function println(x) {
        let output = document.getElementById("current-output");
        output.innerText += x + "\n";
      }

      function display(type, message) {
        let item = document.createElement('div');
        item.className += type;
        item.textContent = message;
        output.append(item);
      }

      function get_input(x) {
        return prompt(x)
      }

      function print_error(x) {
        let item = document.createElement('div');
        item.className += "error";
        item.textContent = x;
        output.append(item);
      }

      function print_info(x) {
        let item = document.createElement('div');
        item.className += "info";
        item.textContent = x;
        output.append(item);
      }

      function plot(f) {
        let plot = document.createElement('div');
        output.append(plot);
        let canvasPlot = Plot(Plot.Renderer.Svg(plot), {
            background: {
                color: '#ffffff'
            },
            line:{
                size: 3,
                color: '#ff0000'
            },
            axes: {
                x: {
                    color: '#000000',
                    ticks: {color: 'rgba(0,0,0,0.5)', step: 0.5}
                },
                y: {
                    color: '#000000',
                    ticks: {color: 'rgba(0,0,0,0.5)', step: 0.5}
                }
            }
        });

        canvasPlot
            .graph((x) => { if (x > 0) { return null; } else { return x; } }, -3, 3);
      }

      function fakeCode(codeText) {
        let code = document.getElementById("input");
        code.innerText = codeText;
        Prism.highlightElement(code);
        runCode();
      }

          let code = document.getElementById("input");
          let outputs = document.getElementById("outputs");
          let liveError = document.getElementById("live-error");
          window.consoleOutput = "";

          window.runCode = function() {
            if(window.crashed)
              return

            let text = code.innerText;
            if(!text)
              return;
            let cloned = input.cloneNode(true);
            cloned.id = null;
            cloned.contentEditable = "false";

            let container = document.createElement('div');
            container.append(cloned);
            container.className += "container";

            let output = document.createElement('pre');
            output.className += "output-value"
            output.id = "current-output"

            // outputs.removeChild(input);
            outputs.replaceChild(container, input);
            container.append(output);

            if(interpreter) {
                try {
                  let out = interpreter.run_and_format(text)

                  if(out)
                    output.innerText += out
                } catch(e) {
                  if(typeof e === "string")
                    print_error("Error: " + e)
                  else {
                    print_error("Error: Interpreter encountered an unrecoverable error")
                    editoresque.destroy();
                    document.getElementById("input").contentEditable = false;
                    window.crashed = true
                  }
                }
          }

            output.id = null

            outputs.append(input);
            code.focus();
            code.innerText = "";
          }

          let input = document.getElementById('input');
          window.editoresque = new Misbehave(input, {
            softTabs: 4,
            oninput: (text, s) => {
                if(typeof interpreter !== 'undefined') {
                try {
                  interpreter.test_and_format(text)
                  liveError.style.visibility = "hidden"
                } catch(e) {
                  liveError.style.visibility = "visible"
                  if(window.crashed)
                    liveError.innerText =
                        "Error: Playpen instance crashed and cannot accept new commands"
                  else
                    liveError.innerText = "Error: " + e
                }
                Prism.highlightElement(input);
            }
            },
          })

          // document.getElementById("run-button").addEventListener("click", runCode);
          editoresque.keys.bind('shift+enter', editoresque.keys.callbacks["enter"][0].callback);
          editoresque.keys.bind('enter', runCode);

