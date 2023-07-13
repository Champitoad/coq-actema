<style>
.pi-expression {
    position: absolute;
}

.pi-expression.dragged,
.pi-expression.dragged:hover,
.pi-expression.dragged:active {
    color: #fff !important;
    background-color: green !important;
    border-color: green !important;
}

.pi-expression:hover,
.pi-expression:active {
    background-color: rgba(0, 0, 0, 0) !important;
    border-color: green !important;
    color: green !important;
    cursor: pointer;
}
</style>

<template>
    <div class="btn btn-outline-success pi-btn pi-expression" :class="{'in-work-zone' : isInWorkZone(), 'in-hypothesis-zone' : !isInWorkZone()}" :data-handle="expression.handle" draggable="true" v-html="html" @mousedown="mousedown" @mouseup="mouseup" @dragstart="dragStart" @dragend="dragEnd" @touchstart="touchstart" @touchend="touchend" v-touch:tap="tap" :id="uniqId()"></div>
</template>

<script>
import _ from "lodash";
import ButtonVue from "./button.vue";

export default {
    extends: ButtonVue,
    props: ["expression", "selectMode", "displayMode"],
    computed: {
        alignment() {
            return "left";
        }
    },
    methods: {
        is: function(str) {
            return str == "expression"; // Bad, allow to break polymorphism
        },

        isLoading() {
            return false;
        },

        toHTML: function() {
            return this.expression.html();
        },

        toString: function() {
            return this.expression.name;
        },

        toMathML: function() {
            return this.expression.mathml();
        },

        setMetadata: function(metadata) {
            this.expression.setmeta(metadata);
        },

        getMetadata: function() {
            return this.expression.getmeta();
        },

        getSubGoal: function(e) {
            return this.expression.parent;
        },

        getHandle: function(e) {
            return this.expression.handle;
        },

        getRootId: function() {
            return this.getRootIdForType("Vh")
        },

        getPosition() {
            return this.expression.position;
        },

        // override button.assignStaticPosition
        assignPosition() {
            if (this.hasSavedPosition()) {
                this.restoreSavedPosition();
            } else {
                this.assignStaticPosition();
            }
        },

        dragStart: function(e) {},

        dragEnd: function(e) {},
        /*
        dragStart: function(predicate, e) {
            // save the handle of the predicate into the event
            e.dataTransfer.setData("handle", predicate.handle);

            // also save the current mouse position relative to the predicate, so we can "correct" the position
            // at drop time (otherwise, it will align, at drop time, the top-left corner to the mouse position)
            var predicateDiv = $(`.pi-expression[data-handle='${predicate.handle}']`);
            var offset = predicateDiv.offset();

            var deltaX = offset.left - e.clientX;
            var deltaY = offset.top  - e.clientY;
            e.dataTransfer.setData("deltaX", deltaX);
            e.dataTransfer.setData("deltaY", deltaY);
        },

        dragEnd: function() {
            this.$forceUpdate();
        },
        */

        getCurrentZone: function() {
            if (this.isInWorkZone()) {
                return "work-zone";
            } else {
                return "hypothesis-zone";
            }
        },

        quickSwitchToWorkZone: function() {
            var c = this.getCoord();
            this.setAbsolutePosition(c.x, c.y);
            $(this.$el)
                .removeClass("in-hypothesis-zone")
                .addClass("in-work-zone");
            var clone = $(this.$el).clone();
            clone.appendTo(this.$proofCanvas.getWorkZone());
            $(this.$el).remove();
            clone.mousedown();
        },

        /*
        getActions(kind, source, dest) {
            // crash the miniprover if we require actions from an expression
        }
        */
    }
};
</script>

