<template>
    <div>
        <div class="container-fluid">
            <!-- Top bar -->
            <div class="row" style="padding-top: 20px; padding-bottom: 20px; background-color: #eee;">
                <button id="done" class="btn btn-info ml-2" @click="done" title="Done" :disabled="!connected">Done</button>
                <div class="mx-auto"></div>
                <div class="buttons text-right mr-2">
                    <button class="btn btn-outline-secondary btn-speech" @click="toggleSpeechRecognition" :disabled="!connected" title="Toggle Speech Recognition"><i class="fas fa-microphone fa-sm"></i></button>
                    <button class="btn btn-outline-secondary btn-select" @click="toggleSelectionMode" :disabled="!connected" title="Toggle Selection Mode (shift)"><i class="fas fa-mouse-pointer fa-sm"></i></button>
                    <button class="btn btn-outline-secondary btn-undo" @click="undo" :disabled="!connected" title="Undo (ctrl+z)"><i class="fas fa-undo"></i></button>
                    <button class="btn btn-outline-secondary btn-redo" @click="redo" :disabled="!connected" title="Undo (ctrl+y)"><i class="fas fa-redo"></i></button>
                </div>
            </div>
            <!-- Proof canvas -->
            <div class="row" style="height: calc(100vh - 78px)">
                <div class="container-fluid pi-canvas" id="prover-canvas" style="padding-left: 0; padding-right: 0;">
                    <proof-canvas ref="proofCanvas"></proof-canvas>
                </div>
            </div>
        </div>
    </div>
</template>

<script>
import ProofCanvas from "./components/proofCanvas.vue";
import Vue from "vue";

const vue2TouchEvents = require("vue2-touch-events");
Vue.use(vue2TouchEvents);


//https://www.30secondsofcode.org/js/s/levenshtein-distance/
const levenshteinDistance = (s, t) => {
    if (!s.length) return t.length;
    if (!t.length) return s.length;
    const arr = [];
    for (let i = 0; i <= t.length; i++) {
      arr[i] = [i];
      for (let j = 1; j <= s.length; j++) {
        arr[i][j] =
          i === 0
            ? j
            : Math.min(
                arr[i - 1][j] + 1,
                arr[i][j - 1] + 1,
                arr[i - 1][j - 1] + (s[j - 1] === t[i - 1] ? 0 : 1)
              );
      }
    }
    return arr[t.length][s.length];
  };

//https://gist.github.com/janosh/099bd8061f15e3fbfcc19be0e6b670b9
const argFact = (compareFn) => (array) => array.map((el, idx) => [el, idx]).reduce(compareFn)[1]
const argMin = argFact((max, el) => (el[0] < max[0] ? el : max))

export default {
    components: {
        ProofCanvas,
    },
    created() {
        // update proof canvas with new goal when action request is received
        window.ipcRenderer.on("action", (_, goalsb) => {
            try {
                this.connected = true;
                var proofState = engine.setgoalsb(goalsb);
                this.$refs.proofCanvas.setProofState(proofState);
            } catch (e) {
                this.$refs.proofCanvas.showErrorMessage(e);
                window.ipcRenderer.send('error', this.$refs.proofCanvas.errorMsg);
            }
        });
        // trigger fireworks when qed request is received
        window.ipcRenderer.on("qed", _ => {
            this.$refs.proofCanvas.QED();
            this.connected = false;
        });
        window.ipcRenderer.on("error", (_, msg) => {
            this.$refs.proofCanvas.showErrorMessage(msg);
        });

        window.ipcRenderer.on("TEST", (_, s) => {
            console.log(s);
            var l = this.$refs.proofCanvas.getContextualActions();
            var n = l.length;
            if (n){


                
                const keywords = [];
                    
                    for (let i = 0; i < n; i++) {
                        keywords[i] = l[i].description.toLowerCase();
                    }

                const arr = [];
                    var n = keywords.length;
                    for (let i = 0; i < n; i++) {
                    arr[i] = levenshteinDistance(s, keywords[i]);
                    }
                    console.log(arr);

                    var elem = l[argMin(arr)];
                    console.log(elem.description.toLowerCase());
                    this.$refs.proofCanvas.sendActionCode(elem.action);
                    
            }

        });
    },
    updated() {
    },
    mounted() {
        window.vue = this; // for debug purposes

        // also capture ctrl+z and ctrl+y and M for MathML
        var self = this;
        $(document).keydown(function (e) {
            if (!$('input[type="text"]').is(":focus")) {
                // dont capture on textboxes
                if (e.key === "y" && e.ctrlKey) {
                    // ctrl+y
                    self.redo();
                } else if (e.key === "z" && e.ctrlKey) {
                    // ctrl+z
                    self.undo();
                } else if (e.key === "m" && e.ctrlKey) {
                    self.toggleDisplayMode();
                }
            }

            if (e.key == "Shift" && !e.ctrlKey) {
                // shift
                self.enterSelectionMode();
            }
        });

        $(document).keyup(function (e) {
            if (e.key == "Shift" || e.keyCode === 27) {
                // release shift or escape
                self.exitSelectionMode();
            }
        });
    },
    data() {
        return {
            connected: false,
            speechEnabled: false,
        };
    },

    methods: {
        toggleSpeechRecognition() {
            if (this.speechEnabled) {
                this.speechEnabled = false;
                $(".btn-speech").removeClass("active");
                window.ipcRenderer.send('stopSpeechRecognition');
            } else {
                this.speechEnabled = true;
                $(".btn-speech").addClass("active");
                window.ipcRenderer.send('startSpeechRecognition');
            }
        },

        toggleSelectionMode() {
            if (this.$refs.proofCanvas.selectMode) {
                this.exitSelectionMode();
            } else {
                this.enterSelectionMode();
            }
        },

        enterSelectionMode() {
            this.$refs.proofCanvas.enterSelectMode();
        },

        exitSelectionMode() {
            this.$refs.proofCanvas.exitSelectMode();
        },

        toggleDisplayMode() {
            if (this.$refs.proofCanvas.displayMode === "html") {
                this.setDisplayMode("mathml");
            } else {
                this.setDisplayMode("html");
            }
        },

        setDisplayMode(mode) {
            this.$refs.proofCanvas.setDisplayMode(mode);
        },

        undo() {
            this.$refs.proofCanvas.sendUndo();
        },

        redo() {
            this.$refs.proofCanvas.sendRedo();
        },

        sendProof() {
            try {
                let proofb = window.goal.getproofb();
                window.ipcRenderer.send('action', proofb);
            } catch (e) {
                this.$refs.proofCanvas.showErrorMessage(e);
                window.ipcRenderer.send('error', this.$refs.proofCanvas.errorMsg);
            }
        },

        done() {
            try {
                window.ipcRenderer.send('done');
                this.connected = false;
                this.$refs.proofCanvas.setProofState(null);
            } catch (e) {
                this.$refs.proofCanvas.showErrorMessage(e);
                window.ipcRenderer.send('error', this.$refs.proofCanvas.errorMsg);
            }
        },
    },
};
</script>

<style>
.html,
body {
    margin: 0;
    padding: 0;
    height: 100vh;
    overflow: hidden;
}

span.MJXc-display,
span.MJXc-display * {
    -webkit-touch-callout: none;
    -webkit-user-select: none;
    -khtml-user-select: none;
    -moz-user-select: none;
    -ms-user-select: none;
    user-select: none;
}

div.formula_box {
    position: absolute;
    font: 30pt arial;
    border: 1px solid;
    margin: 0pt;
    padding: 0.3em;
    display: inline;
}

div.formula {
    font: 30pt arial;
    display: inline;
}

div.qed {
    font: 100pt arial;
    display: inline;
}

.btn:focus {
    box-shadow: none !important;
    outline: none !important;
}
</style>
