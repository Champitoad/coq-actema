<template>
    <div>
        <div class="container-fluid">
            <div class="row" style="padding-top: 20px; padding-bottom: 20px; background-color: #eee;">
                <button id="done" class="btn btn-info ml-2" @click="done" title="Done"
                    :disabled="!connected">Done</button>
                <div class="mx-auto"></div>
                <div class="buttons text-right mr-2">
                    <button class="btn btn-outline-secondary btn-select" @click="toggleSelectionMode"
                        :disabled="!connected" title="Toggle selection mode (shift+click)">
                        <i class="fas fa-mouse-pointer fa-sm"></i></button>
                    <button class="btn btn-outline-secondary btn-undo" @click="undo" :disabled="!connected"
                        title="Undo (ctrl+z)"><i class="fas fa-undo"></i></button>
                    <button class="btn btn-outline-secondary btn-redo" @click="redo" :disabled="!connected"
                        title="Redo (ctrl+y)"><i class="fas fa-redo"></i></button>
                </div>
            </div>
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

export default {
    components: {
        ProofCanvas,
    },
    created() {
        // update the lemma database when lemmas are received.
        window.ipcRenderer.on('received_lemmas', (_, datab) => {
            try {
                console.log("Received lemmas");

                let proofState = this.$refs.proofCanvas.getProofState();
                let subgoal_idx = this.$refs.proofCanvas.getActiveSubgoal();
                let lemmaSearch = this.$refs.proofCanvas.$refs.lsearch[subgoal_idx];

                // Load the lemmas in the proof engine.
                proofState = proofState.loadlemmas(datab);
                // Filter the lemma database.            
                //let selection = this.$refs.proofCanvas.getActiveSelection();
                //let pattern = lemmaSearch.getLemmaSearchText();
                //proofState = proofState.filterlemmas(selection, pattern);
                // Load the new proof engine.
                this.$refs.proofCanvas.setProofState(proofState);

                // Once the new proof engine is loaded, update the lemma search bar.
                lemmaSearch.updateLemmaList();
            } catch (e) {
                this.$refs.proofCanvas.showErrorMessage(e);
                window.ipcRenderer.send('error', this.$refs.proofCanvas.errorMsg);
            }
        });
        // update proof canvas with new goal when action request is received
        window.ipcRenderer.on('action', (_, goalsb) => {
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
        window.ipcRenderer.on('qed', _ => {
            this.$refs.proofCanvas.QED();
            this.connected = false;
        });
        window.ipcRenderer.on("error", (_, msg) => {
            this.$refs.proofCanvas.showErrorMessage(msg);
        });
    },
    updated() {
    },
    mounted() {
        window.vue = this; // for debug purposes

        // also capture ctrl+z and ctrl+y and M for MathML
        var self = this;
        $(document).keydown(function (e) {
            if (e.key === "y" && e.ctrlKey) {
                // ctrl+y
                self.redo();
            } else if (e.key === "z" && e.ctrlKey) {
                // ctrl+z
                self.undo();
            } else if (e.key === "m" && e.ctrlKey) {
                // ctrl+m
                self.toggleDisplayMode();
            }
            else if (e.key === "f" && e.ctrlKey) {
                // ctrl+f
                let subgoal_idx = self.$refs.proofCanvas.getActiveSubgoal();
                let lemmaSearch = self.$refs.proofCanvas.$refs.lsearch[subgoal_idx];
                lemmaSearch.searchLemmas();
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
        };
    },

    methods: {
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

        // Called when the "Done" button is clicked.
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
